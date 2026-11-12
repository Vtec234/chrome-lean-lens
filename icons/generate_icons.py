#!/usr/bin/env python3
"""
Generate extension icons for Lean Lens: a magnifying lens (cyan ring, violet handle)
with an amber "goal" dot, on Lean's dark slate background.

Run from the repository root:  python3 icons/generate_icons.py
"""
from PIL import Image, ImageDraw

BG = (28, 32, 52, 255)          # dark slate
BORDER = (88, 101, 242, 255)    # indigo
CYAN = (56, 189, 248, 255)      # lens ring
VIOLET = (168, 85, 247, 255)    # handle
AMBER = (251, 191, 36, 255)     # goal dot

# Geometry in the 0..1 square.
LENS_C = (0.44, 0.44)
LENS_R = 0.215
RING_W = 0.085
HANDLE = ((0.605, 0.605), (0.775, 0.775))
HANDLE_W = 0.11
DOT_R = 0.075


def draw_icon(size):
    # Draw at 4x and downsample for smooth edges at small sizes.
    k = 4
    S = size * k
    img = Image.new("RGBA", (S, S), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)

    pad = max(k, int(S * 0.06))
    d.rounded_rectangle([pad, pad, S - pad - 1, S - pad - 1], radius=int(S * 0.22),
                        fill=BG, outline=BORDER, width=max(k, int(S * 0.04)))

    (x0, y0), (x1, y1) = HANDLE
    w = int(S * HANDLE_W)
    d.line([(x0 * S, y0 * S), (x1 * S, y1 * S)], fill=VIOLET, width=w)
    r = w / 2  # round caps
    for (x, y) in HANDLE:
        d.ellipse([x * S - r, y * S - r, x * S + r, y * S + r], fill=VIOLET)

    cx, cy = LENS_C[0] * S, LENS_C[1] * S
    R = LENS_R * S
    d.ellipse([cx - R, cy - R, cx + R, cy + R], fill=BG, outline=CYAN, width=int(S * RING_W))

    dr = DOT_R * S
    d.ellipse([cx - dr, cy - dr, cx + dr, cy + dr], fill=AMBER)

    return img.resize((size, size), Image.LANCZOS)


SVG = """<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 128 128" width="128" height="128">
  <defs>
    <linearGradient id="bgGrad" x1="0%" y1="0%" x2="100%" y2="100%">
      <stop offset="0%" stop-color="#1f2438"/>
      <stop offset="100%" stop-color="#111422"/>
    </linearGradient>
    <linearGradient id="ring" x1="0%" y1="0%" x2="100%" y2="100%">
      <stop offset="0%" stop-color="#38bdf8"/>
      <stop offset="100%" stop-color="#0284c7"/>
    </linearGradient>
    <linearGradient id="handle" x1="0%" y1="0%" x2="100%" y2="100%">
      <stop offset="0%" stop-color="#c084fc"/>
      <stop offset="100%" stop-color="#7c3aed"/>
    </linearGradient>
  </defs>
  <rect x="8" y="8" width="112" height="112" rx="26" fill="url(#bgGrad)" stroke="#6366f1" stroke-width="4"/>
  <path d="M 77 77 L 99 99" stroke="url(#handle)" stroke-width="14" stroke-linecap="round"/>
  <circle cx="56" cy="56" r="27.5" fill="#1c2034" stroke="url(#ring)" stroke-width="11"/>
  <circle cx="56" cy="56" r="9.5" fill="#fbbf24"/>
</svg>
"""


def main():
    for s in [16, 32, 48, 128]:
        draw_icon(s).save(f"icons/icon{s}.png", "PNG")
        print(f"Generated icons/icon{s}.png")
    with open("icons/icon.svg", "w") as f:
        f.write(SVG)
    print("Generated icons/icon.svg")


if __name__ == "__main__":
    main()
