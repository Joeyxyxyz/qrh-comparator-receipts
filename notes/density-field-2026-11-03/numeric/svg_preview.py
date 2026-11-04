#!/usr/bin/env python3
"""Rough rasteriser (PIL) for the SVG subset written by make_svg.py - for a visual check only."""
import re, sys, xml.etree.ElementTree as ET
from PIL import Image, ImageDraw, ImageFont
SC = 2
src, dst = sys.argv[1], sys.argv[2]
root = ET.parse(src).getroot()
vb = [float(v) for v in root.get("viewBox").split()]
W, H = int(vb[2] * SC), int(vb[3] * SC)
im = Image.new("RGB", (W, H), "#ffffff")
dr = ImageDraw.Draw(im)
FONTS = {}
def font(size, bold=False):
    key = (round(size * SC), bold)
    if key not in FONTS:
        p = "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf" if bold else "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf"
        try: FONTS[key] = ImageFont.truetype(p, key[0])
        except Exception: FONTS[key] = ImageFont.load_default()
    return FONTS[key]
def tag(e): return e.tag.split("}")[-1]
def f(v, d=0.0): return float(v) if v is not None else d
for e in root.iter():
    t = tag(e)
    if t == "rect":
        x, y, w, h = f(e.get("x")), f(e.get("y")), f(e.get("width")), f(e.get("height"))
        fill = e.get("fill"); stroke = e.get("stroke")
        dr.rectangle([x*SC, y*SC, (x+w)*SC, (y+h)*SC], fill=fill if fill and fill != "none" else None, outline=stroke if stroke else None)
    elif t == "line":
        dr.line([f(e.get("x1"))*SC, f(e.get("y1"))*SC, f(e.get("x2"))*SC, f(e.get("y2"))*SC], fill=e.get("stroke"), width=max(1, round(f(e.get("stroke-width"), 1)*SC)))
    elif t == "polyline":
        pts = [tuple(float(c)*SC for c in p.split(",")) for p in e.get("points").split()]
        if len(pts) > 1:
            dr.line(pts, fill=e.get("stroke"), width=max(1, round(f(e.get("stroke-width"), 1)*SC)), joint="curve")
    elif t == "circle":
        cx, cy, r = f(e.get("cx"))*SC, f(e.get("cy"))*SC, f(e.get("r"))*SC
        dr.ellipse([cx-r, cy-r, cx+r, cy+r], fill=e.get("fill"))
    elif t == "path":
        d = e.get("d"); x = y = 0.0; pts = []
        for cmd, args in re.findall(r"([MVHaZ])([^MVHaZ]*)", d):
            nums = [float(v) for v in re.findall(r"-?\d+\.?\d*", args)]
            if cmd == "M": x, y = nums[0], nums[1]; pts.append((x, y))
            elif cmd == "V": y = nums[0]; pts.append((x, y))
            elif cmd == "H": x = nums[0]; pts.append((x, y))
            elif cmd == "a": x += nums[5]; y += nums[6]; pts.append((x, y))
        if len(pts) > 2:
            dr.polygon([(px*SC, py*SC) for px, py in pts], fill=e.get("fill"))
    elif t == "text" and e.text:
        size = f(e.get("font-size"), 12); bold = e.get("font-weight") == "600"
        fnt = font(size, bold); fill = e.get("fill", "#000")
        anchor = {"middle": "ms", "end": "rs"}.get(e.get("text-anchor"), "ls")
        tr = e.get("transform")
        if tr and "rotate(-90)" in tr:
            tx, ty = [float(v) for v in re.search(r"translate\(([-\d.]+),([-\d.]+)\)", tr).groups()]
            tw = int(dr.textlength(e.text, font=fnt)) + 4; th = int(size*SC*1.4)
            tmp = Image.new("RGBA", (tw, th), (0, 0, 0, 0)); ImageDraw.Draw(tmp).text((tw/2, th*0.75), e.text, font=fnt, fill=fill, anchor="ms")
            rot = tmp.rotate(90, expand=True)
            im.paste(rot, (int(tx*SC - rot.width*0.75), int(ty*SC - rot.height/2)), rot)
        else:
            dr.text((f(e.get("x"))*SC, f(e.get("y"))*SC), e.text, font=fnt, fill=fill, anchor=anchor)
im.save(dst)
print("saved", dst, im.size)
