#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Generador automático de videos de fútbol para YouTube (coste $0).

Uso:
    python main.py --tema "El escándalo del árbitro Guruceta" --categoria polemica

Resultado:
    youtube_upload.zip  ->  video.mp4 + miniatura.png + info_youtube.txt

Arquitectura (cada etapa tiene "plan B" para que un fallo puntual no tumbe todo):
    1. Guion .......... g4f  ->  Pollinations (HTTP)  ->  Wikipedia (texto real)
    2. Voz en off ..... edge-tts (por sección, con reintentos y cambio de voz)
    3. Subtítulos ..... tiempos reales por palabra de edge-tts (o estimados si no hay)
    4. Imágenes ....... DuckDuckGo -> Bing -> Wikimedia Commons -> tarjetas generadas
    5. Miniatura ...... Pillow (estilo distinto según categoría)
    6. Video .......... FFmpeg puro (bloques con Ken Burns + crossfade, sin MoviePy)
"""
from __future__ import annotations

import argparse
import asyncio
import functools
import hashlib
import html
import io
import json
import math
import os
import random
import re
import shutil
import subprocess
import sys
import time
import zipfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import requests
from PIL import Image, ImageDraw, ImageEnhance, ImageFilter, ImageFont, ImageOps

# ──────────────────────────────────────────────────────────────────────────────
# CONFIGURACIÓN GENERAL
# ──────────────────────────────────────────────────────────────────────────────
W, H, FPS = 1280, 720, 25          # video 16:9 en 720p (ligero para GitHub Actions)
SOLAPE_FR = 12                     # frames de crossfade entre imágenes (~0.5 s)
CLIPS_POR_BLOQUE = 10              # imágenes que se procesan juntas (controla la RAM)
IMG_MIN, IMG_MAX = 5, 10           # imágenes descargadas por video
PAUSA_SECCION = 0.35               # segundos de silencio entre secciones de voz
PALABRAS_POR_MIN = 150             # ritmo medio de locución
PALABRAS_POR_SECCION = 170

VOCES = ["es-MX-JorgeNeural", "es-ES-AlvaroNeural"]   # se alternan si una falla
UA = {"User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                     "(KHTML, like Gecko) Chrome/124.0 Safari/537.36")}

# Ajustes por categoría: tono del guion, segundos por imagen, velocidad de voz y colores
CATEGORIAS = {
    "polemica": dict(
        etiqueta="POLÉMICA", ritmo=5.0, voz_rate="-3%",
        tono=("serio, dramático y tenso; mantén el suspense, presenta los hechos comprobables "
              "y las versiones enfrentadas sin acusar a nadie de delitos sin pruebas"),
        estructura=("gancho tenso en los primeros segundos, contexto, los hechos, versiones "
                    "enfrentadas, consecuencias y cierre con una pregunta al espectador"),
        paleta=dict(bg1=(8, 0, 0), bg2=(150, 12, 12), texto=(255, 255, 255),
                    acento=(255, 45, 45), trazo=(0, 0, 0)),
    ),
    "historia": dict(
        etiqueta="HISTORIA", ritmo=6.0, voz_rate="+0%",
        tono=("de documental cronológico, narrativo y épico, con orden temporal claro y "
              "frases que crean atmósfera"),
        estructura=("orden cronológico: contexto de la época, antecedentes, desarrollo en "
                    "orden temporal, momento clímax y legado"),
        paleta=dict(bg1=(24, 14, 6), bg2=(128, 92, 48), texto=(244, 204, 120),
                    acento=(255, 232, 170), trazo=(34, 18, 6)),
    ),
    "curiosidades": dict(
        etiqueta="CURIOSIDADES", ritmo=3.0, voz_rate="+6%",
        tono=("dinámico, estilo 'Top' o lista en cuenta regresiva, directo al grano, con datos "
              "sorprendentes y frases cortas"),
        estructura=("formato Top en cuenta regresiva: cada sección es un dato sorprendente "
                    "distinto y el último es el más impactante"),
        paleta=dict(bg1=(0, 36, 140), bg2=(0, 176, 255), texto=(255, 230, 0),
                    acento=(255, 255, 255), trazo=(0, 0, 0)),
    ),
}

EFECTOS = ["zoom_in", "pan_der", "zoom_out", "pan_izq", "diag"]


# ──────────────────────────────────────────────────────────────────────────────
# UTILIDADES
# ──────────────────────────────────────────────────────────────────────────────
def log(msg: str) -> None:
    print(f"[{time.strftime('%H:%M:%S')}] {msg}", flush=True)


def reintentar(intentos: int = 3, espera: float = 2.0):
    """Decorador: repite la función si lanza una excepción (espera creciente)."""
    def deco(fn):
        @functools.wraps(fn)
        def envoltura(*a, **k):
            ultimo = None
            for i in range(1, intentos + 1):
                try:
                    return fn(*a, **k)
                except Exception as e:  # noqa: BLE001
                    ultimo = e
                    log(f"  ! {fn.__name__} intento {i}/{intentos} falló: {str(e)[:160]}")
                    if i < intentos:
                        time.sleep(espera * i)
            raise ultimo
        return envoltura
    return deco


def ejecutar(cmd: list[str], cwd: Path | None = None, desc: str = "ffmpeg") -> None:
    """Ejecuta un comando y lanza un error legible si falla."""
    r = subprocess.run(cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if r.returncode != 0:
        raise RuntimeError(f"{desc} falló (código {r.returncode}):\n{r.stderr[-1500:]}")


def duracion_media(ruta: Path) -> float:
    """Duración en segundos de un archivo de audio/video (ffprobe)."""
    r = subprocess.run(
        ["ffprobe", "-v", "error", "-show_entries", "format=duration",
         "-of", "default=nw=1:nk=1", str(ruta)],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    return float(r.stdout.strip())


def fmt_tiempo(seg: float) -> str:
    seg = int(round(seg))
    return f"{seg // 60}:{seg % 60:02d}"


def quitar_emojis(t: str) -> str:
    return re.sub(r"[\U00010000-\U0010ffff\u2600-\u27bf\ufe0f]", "", t)


# ──────────────────────────────────────────────────────────────────────────────
# 1. GUION Y METADATOS  (g4f -> Pollinations -> Wikipedia)
# ──────────────────────────────────────────────────────────────────────────────
MODELOS_G4F = ["gpt-4o-mini", "gpt-4o", "llama-3.3-70b", "mixtral-8x7b", ""]
SISTEMA = ("Eres un guionista experto de YouTube especializado en fútbol. Escribes en español "
           "neutro. Nunca inventes datos: si no estás seguro de una fecha, cifra o cita, "
           "omítela o exprésala con cautela. No acuses a nadie de delitos sin pruebas.")


def _llm_g4f(mensajes: list[dict], timeout: int = 120) -> str:
    """Proveedor 1: GPT4Free. Prueba varios modelos; corta si se cuelga."""
    from g4f.client import Client  # import perezoso: si no está instalado, pasa al plan B
    ultimo = None
    for modelo in MODELOS_G4F:
        ex = ThreadPoolExecutor(max_workers=1)
        try:
            cliente = Client()
            kw = {"model": modelo, "messages": mensajes} if modelo else {"messages": mensajes}
            fut = ex.submit(lambda kw=kw: cliente.chat.completions.create(**kw))
            resp = fut.result(timeout=timeout)
            texto = (resp.choices[0].message.content or "").strip()
            if len(texto) > 30:
                return texto
        except Exception as e:  # noqa: BLE001
            ultimo = e
            log(f"    g4f/{modelo or 'auto'} falló: {str(e)[:100]}")
        finally:
            ex.shutdown(wait=False, cancel_futures=True)
    raise RuntimeError(f"g4f sin respuesta útil ({ultimo})")


def _llm_pollinations(mensajes: list[dict], timeout: int = 120) -> str:
    """Proveedor 2: endpoint HTTP gratuito de Pollinations (sin clave)."""
    r = requests.post("https://text.pollinations.ai/",
                      json={"messages": mensajes, "model": "openai", "seed": random.randint(1, 10**6)},
                      headers=UA, timeout=timeout)
    r.raise_for_status()
    texto = r.text.strip()
    if len(texto) < 30:
        raise RuntimeError("respuesta vacía")
    return texto


PROVEEDORES_LLM = [("g4f", _llm_g4f), ("pollinations", _llm_pollinations)]


def llamar_llm(mensajes: list[dict], validar):
    """Pide texto a los proveedores en orden; `validar(texto)` devuelve el dato ya
    procesado o lanza ValueError si la respuesta no sirve (entonces se reintenta)."""
    ultimo = None
    for nombre, fn in PROVEEDORES_LLM:
        for intento in (1, 2):
            try:
                return validar(fn(mensajes))
            except Exception as e:  # noqa: BLE001
                ultimo = e
                log(f"    LLM {nombre} intento {intento} falló: {str(e)[:120]}")
                time.sleep(2)
    raise RuntimeError(f"Ningún proveedor de texto respondió bien ({ultimo})")


def extraer_json(texto: str) -> dict:
    """Saca el primer objeto JSON de una respuesta (aunque venga con ```json ... ```)."""
    texto = re.sub(r"```(?:json)?", "", texto)
    ini, fin = texto.find("{"), texto.rfind("}")
    if ini < 0 or fin <= ini:
        raise ValueError("no hay JSON")
    return json.loads(texto[ini:fin + 1], strict=False)


def limpiar_narracion(t: str) -> str:
    """Deja el texto listo para locución: sin markdown, emojis, URLs ni acotaciones."""
    t = re.sub(r"```.*?```", " ", t, flags=re.S)
    t = re.sub(r"https?://\S+", " ", t)
    t = re.sub(r"\[[^\]]*\]", " ", t)
    t = re.sub(r"\((?:[^)]{0,40})(?:pausa|música|musica|efecto|imagen|sonido)[^)]*\)", " ", t, flags=re.I)
    t = re.sub(r"\*\*([^*]{1,30})\*\*", r"\1", t)
    t = re.sub(r"^\s*(?:secci[oó]n|parte|narraci[oó]n|texto)\s*\d*\s*[:.\-–]\s*", "", t, flags=re.I | re.M)
    t = re.sub(r"[*_`~]+", "", quitar_emojis(t))
    t = re.sub(r"[#>|]+", " ", t)
    t = re.sub(r"\s+([.,;:!?])", r"\1", t)
    return re.sub(r"\s+", " ", t).strip()


def limpiar_descripcion(t: str) -> str:
    """Como limpiar_narracion, pero conserva los saltos de párrafo (para la descripción)."""
    parrafos = [limpiar_narracion(p) for p in re.split(r"\n\s*\n|\\n\\n", str(t))]
    return "\n\n".join(p for p in parrafos if p)


def _validar_esquema(texto: str, n: int) -> dict:
    d = extraer_json(texto)
    secs = d.get("secciones")
    if not isinstance(secs, list) or len(secs) < 3:
        raise ValueError("esquema sin secciones suficientes")
    d["secciones"] = [
        {"titulo": str(s.get("titulo", f"Parte {i + 1}")).strip(),
         "puntos": str(s.get("puntos", "")).strip(),
         "busqueda": str(s.get("busqueda_imagen", "")).strip()}
        for i, s in enumerate(secs[:n + 2]) if isinstance(s, dict)]
    if not str(d.get("titulo", "")).strip():
        raise ValueError("sin título")
    return d


def _validar_narracion(texto: str) -> str:
    t = limpiar_narracion(texto)
    if len(t.split()) < 60:
        raise ValueError("narración demasiado corta")
    return t


def guion_con_llm(tema: str, categoria: str, minutos: float) -> dict:
    """Guion en dos pasos (esquema + una llamada por sección): más largo y más estable."""
    cfg = CATEGORIAS[categoria]
    n_sec = max(4, round(minutos * PALABRAS_POR_MIN / PALABRAS_POR_SECCION))
    log(f"  Pidiendo esquema ({n_sec} secciones)…")
    prompt = (
        f'Tema del video: "{tema}"\nCategoría: {categoria}. Tono: {cfg["tono"]}.\n'
        f'Estructura: {cfg["estructura"]}.\n'
        f"Duración: {minutos:g} minutos en exactamente {n_sec} secciones.\n"
        "Devuelve ÚNICAMENTE un JSON válido (sin markdown ni texto extra) con esta forma:\n"
        '{"titulo": "título SEO atractivo, máx. 70 caracteres, palabra clave al inicio",\n'
        ' "descripcion": "descripción de YouTube en 2 párrafos (máx. 900 caracteres)",\n'
        ' "tags": ["12 a 18 tags en español, de más a menos relevante"],\n'
        ' "texto_miniatura": "2 a 4 palabras EN MAYÚSCULAS, impactantes",\n'
        ' "secciones": [{"titulo": "...", "puntos": "hechos que cubre (1-2 frases)", '
        '"busqueda_imagen": "3-5 palabras para buscar fotos reales (persona, equipo, estadio, año)"}]}'
    )
    esquema = llamar_llm([{"role": "system", "content": SISTEMA}, {"role": "user", "content": prompt}],
                         lambda t: _validar_esquema(t, n_sec))
    secciones, previos = [], []
    for i, sec in enumerate(esquema["secciones"][:n_sec]):
        log(f"  Escribiendo sección {i + 1}/{n_sec}: {sec['titulo'][:50]}")
        extra = ""
        if i == 0:
            extra = "Empieza con un gancho que atrape en los primeros 5 segundos. "
        if i == n_sec - 1:
            extra += "Cierra invitando a suscribirse y a comentar su opinión. "
        p = (f'Video: "{tema}" ({categoria}). Tono: {cfg["tono"]}.\n'
             f'Secciones ya escritas: {"; ".join(previos) or "ninguna"}.\n'
             f'Escribe SOLO la narración hablada de la sección {i + 1}/{n_sec}: "{sec["titulo"]}". '
             f'Puntos: {sec["puntos"]}.\n'
             f"Requisitos: unas {PALABRAS_POR_SECCION} palabras, un solo párrafo de texto plano listo "
             f"para que lo lea un locutor, sin títulos, viñetas, markdown, emojis ni acotaciones, con "
             f"puntuación natural. {extra}No repitas lo ya dicho.")
        try:
            narr = llamar_llm([{"role": "system", "content": SISTEMA}, {"role": "user", "content": p}],
                              _validar_narracion)
        except Exception as e:  # noqa: BLE001
            log(f"  ! sección {i + 1} descartada: {str(e)[:100]}")
            continue
        secciones.append({"titulo": sec["titulo"], "narracion": narr,
                          "busqueda": sec["busqueda"] or sec["titulo"]})
        previos.append(sec["titulo"])
    if len(secciones) < 3:
        raise RuntimeError("el LLM no logró escribir suficientes secciones")
    return {"titulo": str(esquema["titulo"]), "descripcion": str(esquema.get("descripcion", "")),
            "tags": [str(t) for t in esquema.get("tags", []) if str(t).strip()],
            "texto_miniatura": str(esquema.get("texto_miniatura", "")),
            "secciones": secciones, "origen": "llm"}


def guion_desde_wikipedia(tema: str, categoria: str, minutos: float) -> dict:
    """Plan C: arma el guion con texto real de Wikipedia (menos 'chispa', pero fiable)."""
    log("  Plan C: construyendo guion con Wikipedia…")
    base = "https://es.wikipedia.org/w/api.php"
    r = requests.get(base, params={"action": "query", "list": "search", "srsearch": tema,
                                   "format": "json", "srlimit": 3, "utf8": 1},
                     headers=UA, timeout=20).json()
    textos = []
    for item in r["query"]["search"]:
        d = requests.get(base, params={"action": "query", "prop": "extracts", "explaintext": 1,
                                       "exsectionformat": "plain", "titles": item["title"],
                                       "format": "json", "redirects": 1}, headers=UA, timeout=20).json()
        for p in d["query"]["pages"].values():
            if p.get("extract"):
                textos.append(p["extract"])
    frases = []
    for t in textos:
        t = re.sub(r"==.*?==", " ", t)
        frases += [f.strip() for f in re.split(r"(?<=[.!?])\s+", limpiar_narracion(t)) if len(f.split()) > 4]
    if len(frases) < 12:
        raise RuntimeError("Wikipedia no devolvió texto suficiente")
    n_sec = max(4, round(minutos * PALABRAS_POR_MIN / PALABRAS_POR_SECCION))
    secciones, buf = [], []
    for f in frases:
        buf.append(f)
        if sum(len(x.split()) for x in buf) >= PALABRAS_POR_SECCION and len(secciones) < n_sec:
            secciones.append(" ".join(buf))
            buf = []
    if buf and len(secciones) < n_sec:
        secciones.append(" ".join(buf))
    intro = {"polemica": "Hoy vamos a hablar de una de las historias más tensas del fútbol. ",
             "historia": "Viajemos en el tiempo para recordar una historia inolvidable del fútbol. ",
             "curiosidades": "Prepárate, porque estos datos del fútbol te van a sorprender. "}[categoria]
    secciones[0] = intro + secciones[0]
    secciones[-1] += " Y tú, ¿qué opinas? Déjalo en los comentarios y suscríbete para más fútbol."
    palabras = [w for w in re.findall(r"\w+", tema) if len(w) > 3]
    return {"titulo": f"{tema}: la historia completa", "descripcion": f"{tema}. Todo lo que debes saber.",
            "tags": [tema] + palabras + ["fútbol", "futbol", categoria],
            "texto_miniatura": " ".join(tema.upper().split()[:4]),
            "secciones": [{"titulo": f"Parte {i + 1}", "narracion": s, "busqueda": tema}
                          for i, s in enumerate(secciones)],
            "origen": "wikipedia"}


def generar_guion(tema: str, categoria: str, minutos: float) -> dict:
    """Cadena de respaldo: LLM -> Wikipedia. Si todo falla, aborta con mensaje claro."""
    try:
        return guion_con_llm(tema, categoria, minutos)
    except Exception as e:  # noqa: BLE001
        log(f"  ! Falló la generación con LLM ({str(e)[:140]}). Paso al plan C.")
    try:
        return guion_desde_wikipedia(tema, categoria, minutos)
    except Exception as e:  # noqa: BLE001
        raise RuntimeError(f"No se pudo generar ningún guion: {e}") from e


# ──────────────────────────────────────────────────────────────────────────────
# 2. VOZ EN OFF (edge-tts)  – una sección por vez, con tiempos por palabra
# ──────────────────────────────────────────────────────────────────────────────
async def _tts_async(texto: str, voz: str, rate: str, ruta_mp3: Path) -> list[tuple]:
    """Sintetiza `texto` y devuelve [(inicio, fin, palabra)] relativos a la sección."""
    import edge_tts  # import perezoso
    try:
        com = edge_tts.Communicate(texto, voz, rate=rate, boundary="WordBoundary")
    except TypeError:  # versiones antiguas sin el parámetro `boundary`
        com = edge_tts.Communicate(texto, voz, rate=rate)
    palabras = []
    with open(ruta_mp3, "wb") as f:
        async for ch in com.stream():
            if ch["type"] == "audio":
                f.write(ch["data"])
            elif ch["type"] == "WordBoundary":
                ini = ch["offset"] / 1e7           # unidades de 100 ns -> segundos
                palabras.append((ini, ini + ch["duration"] / 1e7, ch["text"]))
    if ruta_mp3.stat().st_size < 2000:
        raise RuntimeError("edge-tts devolvió audio vacío")
    return palabras


def sintetizar_seccion(texto: str, rate: str, ruta_mp3: Path) -> list[tuple]:
    """Hasta 5 intentos, alternando de voz si una falla."""
    ultimo = None
    for intento in range(5):
        voz = VOCES[intento % len(VOCES)]
        try:
            return asyncio.run(_tts_async(texto, voz, rate, ruta_mp3))
        except Exception as e:  # noqa: BLE001
            ultimo = e
            log(f"  ! voz {voz} intento {intento + 1}/5 falló: {str(e)[:120]}")
            time.sleep(2 * (intento + 1))
    raise RuntimeError(f"edge-tts no funcionó: {ultimo}")


def sintetizar_voz(secciones: list[dict], carpeta: Path, categoria: str) -> dict:
    """Genera la voz de todas las secciones y las une en un único .wav.
    Devuelve la duración total y, por sección, su inicio/fin y los tiempos de cada palabra."""
    rate = CATEGORIAS[categoria]["voz_rate"]
    wavs, info, cursor = [], [], 0.0
    for i, sec in enumerate(secciones):
        log(f"  Voz sección {i + 1}/{len(secciones)}…")
        mp3, wav = carpeta / f"voz_{i:02d}.mp3", carpeta / f"voz_{i:02d}.wav"
        rel = sintetizar_seccion(sec["narracion"], rate, mp3)
        # a wav estándar + una pausa corta al final (también sirve de respiro entre secciones)
        ejecutar(["ffmpeg", "-y", "-hide_banner", "-loglevel", "error", "-i", str(mp3),
                  "-af", f"apad=pad_dur={PAUSA_SECCION}", "-ar", "44100", "-ac", "1", str(wav)],
                 desc="conversión de voz")
        dur = duracion_media(wav)
        info.append({"titulo": sec["titulo"], "texto": sec["narracion"], "inicio": cursor,
                     "fin": cursor + dur, "palabras": [(cursor + a, cursor + b, t) for a, b, t in rel]})
        wavs.append(wav)
        cursor += dur
    lista = carpeta / "lista_voz.txt"
    lista.write_text("".join(f"file '{w.name}'\n" for w in wavs), encoding="utf-8")
    voz = carpeta / "voz.wav"
    ejecutar(["ffmpeg", "-y", "-hide_banner", "-loglevel", "error", "-f", "concat", "-safe", "0",
              "-i", lista.name, "-c", "copy", voz.name], cwd=carpeta, desc="unión de voz")
    return {"ruta": voz, "duracion": duracion_media(voz), "secciones": info}


# ──────────────────────────────────────────────────────────────────────────────
# 3. SUBTÍTULOS (.ass)  – blancos, grandes, borde negro grueso, abajo al centro
# ──────────────────────────────────────────────────────────────────────────────
def _estimar_palabras(texto: str, inicio: float, fin: float) -> list[tuple]:
    """Plan B sin tiempos reales: reparte la duración según la longitud de cada palabra."""
    toks = texto.split()
    pesos = [len(t) + 2 for t in toks]
    util = max(0.5, fin - inicio - PAUSA_SECCION)
    t, out = inicio, []
    for tok, p in zip(toks, pesos):
        d = util * p / sum(pesos)
        out.append((t, t + d, tok))
        t += d
    return out


def _agrupar_frases(palabras: list[tuple], max_pal=7, max_car=38, pausa=0.30) -> list[list[tuple]]:
    """Corta en frases cortas: por pausas naturales, puntuación o longitud."""
    frases, cur = [], []
    for w in palabras:
        if cur:
            hueco = w[0] - cur[-1][1]
            car = sum(len(x[2]) + 1 for x in cur) + len(w[2])
            if (hueco > pausa or len(cur) >= max_pal or car > max_car
                    or re.search(r"[.!?,;:]$", cur[-1][2])):
                frases.append(cur)
                cur = []
        cur.append(w)
    if cur:
        frases.append(cur)
    return frases


def _t_ass(seg: float) -> str:
    seg = max(0.0, seg)
    cs = int(round(seg * 100))
    return f"{cs // 360000}:{cs // 6000 % 60:02d}:{cs // 100 % 60:02d}.{cs % 100:02d}"


def crear_subtitulos(audio: dict, ruta: Path) -> Path:
    """Escribe el archivo .ass sincronizado con la voz."""
    cab = ("[Script Info]\nScriptType: v4.00+\nPlayResX: 1280\nPlayResY: 720\nWrapStyle: 0\n\n"
           "[V4+ Styles]\nFormat: Name, Fontname, Fontsize, PrimaryColour, SecondaryColour, "
           "OutlineColour, BackColour, Bold, Italic, Underline, StrikeOut, ScaleX, ScaleY, Spacing, "
           "Angle, BorderStyle, Outline, Shadow, Alignment, MarginL, MarginR, MarginV, Encoding\n"
           "Style: Sub,DejaVu Sans,54,&H00FFFFFF,&H00FFFFFF,&H00000000,&H00000000,-1,0,0,0,100,100,"
           "0,0,1,6,0,2,70,70,55,1\n\n"
           "[Events]\nFormat: Layer, Start, End, Style, Name, MarginL, MarginR, MarginV, Effect, Text\n")
    lineas = []
    for sec in audio["secciones"]:
        palabras = sec["palabras"] or _estimar_palabras(sec["texto"], sec["inicio"], sec["fin"])
        frases = _agrupar_frases(palabras)
        for k, fr in enumerate(frases):
            ini = fr[0][0]
            fin = fr[-1][1] + 0.12
            if k + 1 < len(frases):
                fin = min(fin, frases[k + 1][0][0])       # nunca se pisan dos subtítulos
            texto = " ".join(w[2] for w in fr).replace("{", "(").replace("}", ")")
            if texto:
                texto = texto[0].upper() + texto[1:]
            lineas.append(f"Dialogue: 0,{_t_ass(ini)},{_t_ass(max(fin, ini + 0.2))},Sub,,0,0,0,,{texto}")
    ruta.write_text(cab + "\n".join(lineas) + "\n", encoding="utf-8")
    log(f"  {len(lineas)} subtítulos escritos")
    return ruta


# ──────────────────────────────────────────────────────────────────────────────
# 4. IMÁGENES  (DuckDuckGo -> Bing -> Wikimedia Commons -> tarjetas generadas)
# ──────────────────────────────────────────────────────────────────────────────
def _urls_duckduckgo(q: str, n: int = 20) -> list[str]:
    s = requests.Session()
    s.headers.update(UA)
    r = s.get("https://duckduckgo.com/", params={"q": q, "iax": "images", "ia": "images"}, timeout=15)
    m = re.search(r"vqd=[\"']?([\d-]+)", r.text)
    if not m:
        raise RuntimeError("DuckDuckGo no entregó token vqd")
    r = s.get("https://duckduckgo.com/i.js", timeout=15, headers={"Referer": "https://duckduckgo.com/"},
              params={"l": "es-es", "o": "json", "q": q, "vqd": m.group(1), "f": ",,,,,", "p": "1"})
    r.raise_for_status()
    return [x["image"] for x in r.json().get("results", []) if x.get("image")][:n]


def _urls_bing(q: str, n: int = 20) -> list[str]:
    r = requests.get("https://www.bing.com/images/search", headers=UA, timeout=15,
                     params={"q": q, "form": "HDRSC2", "first": 1, "qft": "+filterui:imagesize-large"})
    r.raise_for_status()
    urls = [html.unescape(u) for u in re.findall(r"murl&quot;:&quot;(.*?)&quot;", r.text)]
    return urls[:n]


def _urls_commons(q: str, n: int = 20) -> list[str]:
    r = requests.get("https://commons.wikimedia.org/w/api.php", headers=UA, timeout=20,
                     params={"action": "query", "generator": "search", "gsrnamespace": 6,
                             "gsrsearch": q, "gsrlimit": n, "prop": "imageinfo",
                             "iiprop": "url|mime", "iiurlwidth": 1600, "format": "json"})
    r.raise_for_status()
    urls = []
    for p in r.json().get("query", {}).get("pages", {}).values():
        ii = (p.get("imageinfo") or [{}])[0]
        if ii.get("mime") in ("image/jpeg", "image/png"):
            urls.append(ii.get("thumburl") or ii.get("url"))
    return [u for u in urls if u]


FUENTES_IMG = [("duckduckgo", _urls_duckduckgo), ("bing", _urls_bing), ("commons", _urls_commons)]


def candidatas(q: str):
    """Generador perezoso de URLs: si una fuente falla o se agota, sigue con la siguiente."""
    for nombre, fn in FUENTES_IMG:
        try:
            urls = fn(q)
            log(f"    {nombre}: {len(urls)} resultados para «{q}»")
        except Exception as e:  # noqa: BLE001
            log(f"    {nombre} falló para «{q}»: {str(e)[:90]}")
            continue
        yield from urls


@reintentar(intentos=2, espera=1.0)
def _bajar(url: str) -> bytes:
    r = requests.get(url, headers=UA, timeout=15)
    r.raise_for_status()
    if len(r.content) > 15_000_000:
        raise RuntimeError("imagen demasiado pesada")
    return r.content


def _abrir_rgb(datos: bytes) -> Image.Image:
    img = Image.open(io.BytesIO(datos))
    img.load()
    if img.mode in ("RGBA", "LA", "P"):
        img = img.convert("RGBA")
        fondo = Image.new("RGBA", img.size, (255, 255, 255, 255))
        img = Image.alpha_composite(fondo, img)
    img = img.convert("RGB")
    if min(img.size) < 400 or max(img.size) < 700:
        raise ValueError("imagen demasiado pequeña")
    return img


def preparar_imagen(img: Image.Image) -> Image.Image:
    """Deja la imagen en 1920x1080: recorte si ya es panorámica; si no, fondo difuminado."""
    ar = img.width / img.height
    if 1.45 <= ar <= 2.1:
        return ImageOps.fit(img, (1920, 1080), Image.LANCZOS, centering=(0.5, 0.4))
    fondo = ImageOps.fit(img, (480, 270), Image.LANCZOS).filter(ImageFilter.GaussianBlur(7))
    fondo = ImageEnhance.Brightness(fondo.resize((1920, 1080), Image.BILINEAR)).enhance(0.55)
    fg = ImageOps.contain(img, (1920, 1080), Image.LANCZOS)
    fondo.paste(fg, ((1920 - fg.width) // 2, (1080 - fg.height) // 2))
    return fondo


def degradado(w: int, h: int, c1: tuple, c2: tuple) -> Image.Image:
    mascara = Image.linear_gradient("L").resize((w, h))
    return Image.composite(Image.new("RGB", (w, h), c2), Image.new("RGB", (w, h), c1), mascara)


# --- fuentes (Bebas Neue gratis; si no hay red, DejaVu Bold) ---
FUENTE_URLS = [
    "https://github.com/google/fonts/raw/main/ofl/bebasneue/BebasNeue-Regular.ttf",
    "https://raw.githubusercontent.com/google/fonts/main/ofl/bebasneue/BebasNeue-Regular.ttf",
]
FUENTES_RESPALDO = [
    "/usr/share/fonts/truetype/dejavu/DejaVuSansCondensed-Bold.ttf",
    "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
    "/usr/share/fonts/truetype/liberation/LiberationSans-Bold.ttf",
    "C:/Windows/Fonts/impact.ttf", "C:/Windows/Fonts/arialbd.ttf",
    "/Library/Fonts/Arial Bold.ttf",
]
_FUENTE_CACHE: dict = {}


def ruta_fuente() -> Path | None:
    if "ruta" in _FUENTE_CACHE:
        return _FUENTE_CACHE["ruta"]
    destino = Path("fuentes") / "BebasNeue-Regular.ttf"
    if not destino.exists():
        for url in FUENTE_URLS:
            try:
                r = requests.get(url, headers=UA, timeout=20)
                r.raise_for_status()
                if r.content[:4] in (b"\x00\x01\x00\x00", b"OTTO", b"true"):
                    destino.parent.mkdir(exist_ok=True)
                    destino.write_bytes(r.content)
                    break
            except Exception as e:  # noqa: BLE001
                log(f"  ! no se pudo bajar Bebas Neue: {str(e)[:80]}")
    for p in [destino] + [Path(x) for x in FUENTES_RESPALDO]:
        if p.exists():
            _FUENTE_CACHE["ruta"] = p
            return p
    _FUENTE_CACHE["ruta"] = None
    return None


def cargar_fuente(tam: int):
    p = ruta_fuente()
    if p:
        return ImageFont.truetype(str(p), tam)
    try:
        return ImageFont.load_default(tam)
    except TypeError:
        return ImageFont.load_default()


def crear_placeholder(texto: str, ruta: Path, categoria: str, variante: int = 0) -> None:
    """Tarjeta 1920x1080 con degradado y texto: último recurso si no hay imágenes reales."""
    p = CATEGORIAS[categoria]["paleta"]
    img = degradado(1920, 1080, p["bg1"], p["bg2"])
    if variante % 2:
        img = img.transpose(Image.FLIP_TOP_BOTTOM)
    d = ImageDraw.Draw(img)
    f = cargar_fuente(150)
    lineas, cur = [], ""
    for w in texto.upper().split():
        if d.textlength((cur + " " + w).strip(), font=f) <= 1500:
            cur = (cur + " " + w).strip()
        else:
            lineas.append(cur)
            cur = w
    lineas.append(cur)
    y = 540 - len(lineas[:3]) * 90
    for ln in lineas[:3]:
        d.text((960, y), ln, font=f, fill=p["texto"], anchor="mm", stroke_width=8, stroke_fill=p["trazo"])
        y += 180
    img.save(ruta, "JPEG", quality=90)


def _con_sufijo(q: str) -> str:
    q = q.strip()
    return q if re.search(r"f[uú]tbol|football|soccer", q, re.I) else f"{q} fútbol"


def obtener_imagenes(tema: str, guion: dict, carpeta: Path, categoria: str):
    """Descarga entre IMG_MIN e IMG_MAX imágenes. Devuelve (pool, consulta_por_seccion).
    Cada elemento del pool: {path, orig, q, real}. Nunca falla: completa con tarjetas."""
    carpeta.mkdir(parents=True, exist_ok=True)
    queries: list[str] = []
    for q in [tema] + [s["busqueda"] for s in guion["secciones"]]:
        q = _con_sufijo(q)
        if q.lower() not in [x.lower() for x in queries]:
            queries.append(q)
    qs_seccion = [next(i for i, x in enumerate(queries) if x.lower() == _con_sufijo(s["busqueda"]).lower())
                  for s in guion["secciones"]]
    generales = ["fútbol estadio lleno", "soccer match stadium", "balón de fútbol césped"]
    todas = queries + generales
    iters = {i: candidatas(q) for i, q in enumerate(todas)}
    intentos = {i: 0 for i in iters}
    vistos: set[str] = set()
    pool: list[dict] = []
    limite = time.time() + 240                       # presupuesto máximo de tiempo para imágenes

    def tomar(i: int, cuantas: int) -> None:
        ok = 0
        while ok < cuantas and len(pool) < IMG_MAX and intentos[i] < 12 and time.time() < limite:
            try:
                url = next(iters[i])
            except StopIteration:
                intentos[i] = 99
                return
            intentos[i] += 1
            try:
                datos = _bajar(url)
                h = hashlib.md5(datos).hexdigest()
                if h in vistos:
                    continue
                img = _abrir_rgb(datos)
                vistos.add(h)
            except Exception:  # noqa: BLE001
                continue
            n = len(pool)
            ruta, orig = carpeta / f"img_{n:02d}.jpg", carpeta / f"orig_{n:02d}.jpg"
            preparar_imagen(img).save(ruta, "JPEG", quality=90)
            ImageOps.contain(img, (1600, 1600)).save(orig, "JPEG", quality=90)
            pool.append({"path": ruta, "orig": orig, "q": i, "real": True})
            ok += 1
            log(f"    + imagen {n + 1} ({img.width}x{img.height})")

    for _ in range(3):                                # varias pasadas para repartir entre consultas
        for i in range(len(queries)):
            tomar(i, 2)
            time.sleep(0.3)
        if len(pool) >= IMG_MAX:
            break
    if len(pool) < IMG_MIN:                           # consultas generales de refuerzo
        for i in range(len(queries), len(todas)):
            tomar(i, 3)
    reales = len(pool)
    textos = [tema] + [s["titulo"] for s in guion["secciones"]]
    while len(pool) < IMG_MIN:                        # último recurso: tarjetas generadas
        n = len(pool)
        ruta = carpeta / f"img_{n:02d}.jpg"
        crear_placeholder(textos[n % len(textos)], ruta, categoria, n)
        pool.append({"path": ruta, "orig": None, "q": -1, "real": False})
    log(f"  Imágenes: {reales} reales + {len(pool) - reales} tarjetas generadas")
    return pool, qs_seccion


# ──────────────────────────────────────────────────────────────────────────────
# 5. MINIATURA (Pillow)
# ──────────────────────────────────────────────────────────────────────────────
TW, TH = 1280, 720


def _tratar(img: Image.Image, categoria: str) -> Image.Image:
    """Estilo visual de la foto principal según la categoría."""
    if categoria == "historia":                       # sepia
        return ImageOps.colorize(ImageOps.grayscale(img), black=(30, 16, 6), white=(255, 232, 185))
    if categoria == "polemica":                       # contraste alto + tinte rojo
        img = ImageEnhance.Color(ImageEnhance.Contrast(img).enhance(1.3)).enhance(0.7)
        return Image.blend(img, Image.new("RGB", img.size, (170, 0, 0)), 0.2)
    return ImageEnhance.Brightness(ImageEnhance.Color(img).enhance(1.4)).enhance(1.05)   # vivo


def _ajustar_texto(texto: str, max_w: int, max_h: int):
    """Busca el mayor tamaño de letra y reparto en 1-4 líneas que cabe en el área.
    Nunca descarta palabras: si nada cabe, usa 4 líneas con letra pequeña."""
    palabras = texto.split() or ["FÚTBOL"]
    mejor = None
    for n_lin in (1, 2, 3, 4):
        if n_lin > len(palabras):
            break
        k = math.ceil(len(palabras) / n_lin)
        lineas = [" ".join(palabras[i:i + k]) for i in range(0, len(palabras), k)]
        for tam in range(260, 39, -10):
            f = cargar_fuente(tam)
            ancho = max(f.getbbox(ln)[2] for ln in lineas)
            alto = len(lineas) * int(tam * 0.98)
            if ancho <= max_w and alto <= max_h:
                if mejor is None or tam > mejor[0]:
                    mejor = (tam, lineas)
                break
    if mejor:
        return mejor
    k = math.ceil(len(palabras) / 4)
    return 40, [" ".join(palabras[i:i + k]) for i in range(0, len(palabras), k)]


def crear_miniatura(texto: str, categoria: str, pool: list[dict], ruta: Path) -> None:
    cfg = CATEGORIAS[categoria]
    p = cfg["paleta"]
    lienzo = degradado(TW, TH, p["bg1"], p["bg2"])
    orig = next((e["orig"] for e in pool
                 if e.get("orig") and min(Image.open(e["orig"]).size) >= 500), None)
    if orig:
        try:
            ancho = 780
            foto = ImageOps.fit(Image.open(orig).convert("RGB"), (ancho, TH), Image.LANCZOS,
                                centering=(0.5, 0.3))
            foto = _tratar(foto, categoria)
            mascara = Image.new("L", (ancho, TH), 255)           # borde izquierdo difuminado
            mascara.paste(Image.linear_gradient("L").rotate(90).resize((260, TH)), (0, 0))
            lienzo.paste(foto, (TW - ancho, 0), mascara)
        except Exception as e:  # noqa: BLE001
            log(f"  ! no se pudo usar la foto en la miniatura: {str(e)[:80]}")
    sombra = Image.linear_gradient("L").rotate(-90).resize((820, TH)).point(lambda v: int(v * 0.65))
    lienzo.paste(Image.new("RGB", (820, TH), (0, 0, 0)), (0, 0), sombra)   # oscurece zona del texto

    d = ImageDraw.Draw(lienzo)
    tam, lineas = _ajustar_texto(texto.upper(), 700, 500)
    f = cargar_fuente(tam)
    sw = max(6, tam // 11)
    alto_total = len(lineas) * int(tam * 0.98)
    y = (TH - alto_total) // 2 + 30
    for i, ln in enumerate(lineas):
        color = p["acento"] if (len(lineas) > 1 and i == len(lineas) - 1) else p["texto"]
        d.text((58, y + 8), ln, font=f, fill=(0, 0, 0), stroke_width=sw, stroke_fill=(0, 0, 0))
        d.text((50, y), ln, font=f, fill=color, stroke_width=sw, stroke_fill=p["trazo"])
        y += int(tam * 0.98)

    # etiqueta de categoría + marco
    fe = cargar_fuente(50)
    caja = d.textbbox((0, 0), cfg["etiqueta"], font=fe)
    bw, bh = caja[2] - caja[0] + 44, caja[3] - caja[1] + 28
    d.rounded_rectangle([46, 44, 46 + bw, 44 + bh], radius=12, fill=p["acento"])
    lum = 0.3 * p["acento"][0] + 0.59 * p["acento"][1] + 0.11 * p["acento"][2]
    d.text((46 + 22 - caja[0], 44 + 14 - caja[1]), cfg["etiqueta"], font=fe,
           fill=(0, 0, 0) if lum > 140 else (255, 255, 255))
    d.rectangle([0, 0, TW - 1, TH - 1], outline=p["acento"], width=14)

    lienzo.save(ruta, "PNG", optimize=True)
    if ruta.stat().st_size > 1_900_000:               # YouTube admite miniaturas de hasta 2 MB
        lienzo.quantize(colors=256, dither=Image.FLOYDSTEINBERG).save(ruta, "PNG", optimize=True)


# ──────────────────────────────────────────────────────────────────────────────
# 6. VIDEO CON FFMPEG PURO  (Ken Burns + crossfade, por bloques para ahorrar RAM)
# ──────────────────────────────────────────────────────────────────────────────
def expr_efecto(nombre: str, n: int) -> tuple[str, str, str]:
    """Expresiones z/x/y de `zoompan` para cada efecto Ken Burns (n = frames del clip)."""
    n = max(n, 2)
    cx, cy = "iw/2-(iw/zoom/2)", "ih/2-(ih/zoom/2)"
    if nombre == "zoom_in":
        return f"1+0.18*on/{n}", cx, cy
    if nombre == "zoom_out":
        return f"1.18-0.18*on/{n}", cx, cy
    if nombre == "pan_der":
        return "1.15", f"(iw-iw/zoom)*on/{n}", cy
    if nombre == "pan_izq":
        return "1.15", f"(iw-iw/zoom)*(1-on/{n})", cy
    return f"1.05+0.12*on/{n}", f"(iw-iw/zoom)*on/{n}", f"(ih-ih/zoom)*on/{n}"   # diagonal


def planificar_clips(audio: dict, pool: list[dict], qs_seccion: list[int], ritmo: float) -> list[dict]:
    """Reparte la duración exacta del audio en 'huecos' de ~`ritmo` segundos y asigna una
    imagen y un efecto a cada uno. Las imágenes se eligen según la sección que se esté narrando."""
    total_fr = math.ceil(audio["duracion"] * FPS)
    n = max(1, round(audio["duracion"] / ritmo))
    base, resto = divmod(total_fr, n)
    huecos = [base + (1 if i < resto else 0) for i in range(n)]
    secs = audio["secciones"]
    uso = [0] * len(pool)
    clips, t, previa, efecto_prev = [], 0, -1, None
    azar = random.Random(7)
    for i, fr in enumerate(huecos):
        medio = (t + fr / 2) / FPS
        idx_sec = next((k for k, s in enumerate(secs) if s["inicio"] <= medio < s["fin"]), len(secs) - 1)
        cand = [k for k, e in enumerate(pool) if e["q"] == qs_seccion[min(idx_sec, len(qs_seccion) - 1)]]
        cand = cand or [k for k, e in enumerate(pool) if e["real"]] or list(range(len(pool)))
        cand_sin_repetir = [k for k in cand if k != previa] or cand
        k = min(cand_sin_repetir, key=lambda x: (uso[x], azar.random()))
        uso[k] += 1
        efecto = azar.choice([e for e in EFECTOS if e != efecto_prev])
        clips.append({"img": pool[k]["path"], "frames": fr, "efecto": efecto})
        previa, efecto_prev, t = k, efecto, t + fr
    return clips


def render_bloque(clips: list[dict], indice: int, carpeta: Path) -> Path:
    """Un solo FFmpeg para un grupo pequeño de imágenes: zoompan + xfade (crossfade).
    La salida dura (suma de huecos + SOLAPE_FR) para solaparse con el bloque siguiente."""
    salida = carpeta / f"bloque_{indice:03d}.mp4"
    cmd = ["ffmpeg", "-y", "-hide_banner", "-loglevel", "error"]
    for c in clips:
        cmd += ["-i", str(Path(c["img"]).resolve())]
    filtros = []
    for k, c in enumerate(clips):
        nfr = c["frames"] + SOLAPE_FR
        z, x, y = expr_efecto(c["efecto"], nfr)
        filtros.append(f"[{k}:v]zoompan=z='{z}':x='{x}':y='{y}':d={nfr}:s={W}x{H}:fps={FPS},"
                       f"setsar=1,format=yuv420p[v{k}]")
    ultimo, acum = "[v0]", 0
    for k in range(1, len(clips)):
        acum += clips[k - 1]["frames"]
        filtros.append(f"{ultimo}[v{k}]xfade=transition=fade:duration={SOLAPE_FR / FPS:.4f}:"
                       f"offset={acum / FPS:.4f}[x{k}]")
        ultimo = f"[x{k}]"
    cmd += ["-filter_complex", ";".join(filtros), "-map", ultimo, "-c:v", "libx264",
            "-preset", "ultrafast", "-crf", "18", "-pix_fmt", "yuv420p", "-r", str(FPS), str(salida)]
    ejecutar(cmd, desc=f"bloque {indice}")
    return salida


def unir_y_finalizar(bloques: list[Path], frames_bloque: list[int], audio: Path, subs: Path | None,
                     salida: Path, duracion: float, cwd: Path) -> None:
    """Une los bloques con crossfade, quema los subtítulos y mezcla la voz. Una sola codificación final."""
    cmd = ["ffmpeg", "-y", "-hide_banner", "-loglevel", "error"]
    for b in bloques:
        cmd += ["-i", b.name]
    cmd += ["-i", audio.name]
    filtros, ultimo, acum = [], "[0:v]", 0
    for k in range(1, len(bloques)):
        acum += frames_bloque[k - 1]
        filtros.append(f"{ultimo}[{k}:v]xfade=transition=fade:duration={SOLAPE_FR / FPS:.4f}:"
                       f"offset={acum / FPS:.4f}[m{k}]")
        ultimo = f"[m{k}]"
    filtros.append(f"{ultimo}subtitles={subs.name}[vf]" if subs else f"{ultimo}null[vf]")
    cmd += ["-filter_complex", ";".join(filtros), "-map", "[vf]", "-map", f"{len(bloques)}:a",
            "-af", "loudnorm=I=-16:TP=-1.5:LRA=11", "-c:v", "libx264", "-preset", "veryfast",
            "-crf", "22", "-pix_fmt", "yuv420p", "-c:a", "aac", "-b:a", "160k",
            "-t", f"{duracion:.3f}", "-movflags", "+faststart", salida.name]
    ejecutar(cmd, cwd=cwd, desc="render final")


def generar_video(audio: dict, pool: list[dict], qs_seccion: list[int], categoria: str,
                  carpeta: Path, subs: Path | None) -> Path:
    clips = planificar_clips(audio, pool, qs_seccion, CATEGORIAS[categoria]["ritmo"])
    log(f"  {len(clips)} imágenes en pantalla (una cada ~{CATEGORIAS[categoria]['ritmo']:g} s)")
    grupos = [clips[i:i + CLIPS_POR_BLOQUE] for i in range(0, len(clips), CLIPS_POR_BLOQUE)]
    bloques = []
    for i, g in enumerate(grupos):
        log(f"  Bloque {i + 1}/{len(grupos)}…")
        bloques.append(render_bloque(g, i, carpeta))
    frames_bloque = [sum(c["frames"] for c in g) for g in grupos]
    salida = carpeta / "video.mp4"
    log("  Render final (crossfades + subtítulos + voz)…")
    try:
        unir_y_finalizar(bloques, frames_bloque, audio["ruta"], subs, salida, audio["duracion"], carpeta)
    except RuntimeError as e:
        if not subs:
            raise
        log(f"  ! falló con subtítulos ({str(e)[:200]}). Reintento sin subtítulos.")
        unir_y_finalizar(bloques, frames_bloque, audio["ruta"], None, salida, audio["duracion"], carpeta)
    for b in bloques:
        b.unlink(missing_ok=True)
    return salida


# ──────────────────────────────────────────────────────────────────────────────
# 7. METADATOS (.txt) Y EMPAQUETADO (.zip)
# ──────────────────────────────────────────────────────────────────────────────
def limpiar_tags(tags: list[str], tema: str, categoria: str) -> list[str]:
    base = [*tags, "fútbol", "futbol", "historia del fútbol", categoria]
    base += [w for w in re.findall(r"\w+", tema) if len(w) > 4]
    vistos, salida, total = set(), [], 0
    for t in base:
        t = re.sub(r"[<>#\"]", "", quitar_emojis(str(t))).strip()
        if not t or len(t) > 30 or t.lower() in vistos:
            continue
        if total + len(t) + 2 > 480:                  # YouTube limita el total de tags (~500 caracteres)
            break
        vistos.add(t.lower())
        salida.append(t)
        total += len(t) + 2
    return salida


def escribir_info(guion: dict, audio: dict, tema: str, categoria: str, ruta: Path, n_reales: int) -> None:
    titulo = limpiar_narracion(guion["titulo"]).strip(" \"'")[:100] or tema[:100]
    tags = limpiar_tags(guion["tags"], tema, categoria)
    desc = limpiar_descripcion(guion["descripcion"]) or tema
    capitulos = "\n".join(f"{fmt_tiempo(s['inicio'])} {s['titulo']}" for s in audio["secciones"])
    hashtags = " ".join("#" + re.sub(r"\W", "", t.title()) for t in tags[:3] if re.sub(r"\W", "", t))
    texto = (f"TÍTULO (SEO):\n{titulo}\n\n"
             f"DESCRIPCIÓN:\n{desc}\n\nCAPÍTULOS:\n{capitulos}\n\n{hashtags}\n\n"
             f"TAGS (copiar y pegar en YouTube):\n{', '.join(tags)}\n\n"
             f"----- NOTAS PARA TI (no copiar) -----\n"
             f"Guion generado con: {guion['origen']} | Imágenes reales: {n_reales} | "
             f"Duración: {fmt_tiempo(audio['duracion'])}\n"
             f"Revisa los datos del video antes de subirlo: las IAs gratuitas pueden equivocarse.\n"
             f"Las imágenes vienen de buscadores: comprueba que puedes usarlas (derechos de autor).\n")
    ruta.write_text(texto, encoding="utf-8")


def empaquetar_zip(video: Path, miniatura: Path, info: Path, destino: Path) -> None:
    with zipfile.ZipFile(destino, "w", zipfile.ZIP_DEFLATED) as z:
        z.write(video, "video.mp4")
        z.write(miniatura, "miniatura.png")
        z.write(info, "info_youtube.txt")


# ──────────────────────────────────────────────────────────────────────────────
# PROGRAMA PRINCIPAL
# ──────────────────────────────────────────────────────────────────────────────
def main() -> int:
    ap = argparse.ArgumentParser(description="Genera un video de fútbol para YouTube (coste $0).")
    ap.add_argument("--tema", required=True, help='Tema del video, ej. "5 datos curiosos de Pelé"')
    ap.add_argument("--categoria", required=True, choices=list(CATEGORIAS), help="polemica | historia | curiosidades")
    ap.add_argument("--minutos", type=float, default=8.0, help="duración aproximada (opcional, por defecto 8)")
    a = ap.parse_args()
    tema, categoria = a.tema.strip(), a.categoria
    minutos = min(max(a.minutos, 3.0), 20.0)
    if not tema:
        ap.error("--tema no puede estar vacío")

    trabajo = Path("trabajo")
    shutil.rmtree(trabajo, ignore_errors=True)
    trabajo.mkdir()
    t0 = time.time()
    try:
        log(f"▶ Tema: «{tema}» | categoría: {categoria} | ~{minutos:g} min")
        log("1/6 Guion y metadatos…")
        guion = generar_guion(tema, categoria, minutos)
        log(f"    título: {guion['titulo']}  (origen: {guion['origen']})")

        log("2/6 Voz en off…")
        audio = sintetizar_voz(guion["secciones"], trabajo, categoria)
        log(f"    duración de la voz: {fmt_tiempo(audio['duracion'])}")

        log("3/6 Subtítulos…")
        try:
            subs = crear_subtitulos(audio, trabajo / "subs.ass")
        except Exception as e:  # noqa: BLE001
            log(f"  ! sin subtítulos: {e}")
            subs = None

        log("4/6 Imágenes…")
        pool, qs_seccion = obtener_imagenes(tema, guion, trabajo / "img", categoria)

        log("5/6 Miniatura…")
        texto_min = limpiar_narracion(guion["texto_miniatura"]) or " ".join(tema.split()[:4])
        miniatura = trabajo / "miniatura.png"
        try:
            crear_miniatura(texto_min, categoria, pool, miniatura)
        except Exception as e:  # noqa: BLE001
            log(f"  ! miniatura con foto falló ({e}); creo una simple")
            crear_miniatura(texto_min, categoria, [], miniatura)

        log("6/6 Video…")
        video = generar_video(audio, pool, qs_seccion, categoria, trabajo, subs)

        info = trabajo / "info_youtube.txt"
        escribir_info(guion, audio, tema, categoria, info, sum(1 for e in pool if e["real"]))
        empaquetar_zip(video, miniatura, info, Path("youtube_upload.zip"))
        mb = Path("youtube_upload.zip").stat().st_size / 1e6
        log(f"✔ Listo: youtube_upload.zip ({mb:.0f} MB) en {(time.time() - t0) / 60:.1f} min")
        shutil.rmtree(trabajo, ignore_errors=True)
        return 0
    except Exception as e:  # noqa: BLE001
        log(f"✘ ERROR FATAL: {e}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
