"""
Injects GoatCounter analytics into every generated page of the lean
blueprint site, right before </body>. This runs as a build step after
`leanblueprint web` on every push, because blueprint/src/web is fully
regenerated each time and any direct HTML edit would not survive.

Uses the shared "goldenphysics" GoatCounter site code so lean.goldenphysics.org
shows up in the same dashboard as the rest of Golden Physics Project. Because
this is a different hostname sharing one site code, we override the recorded
path to be prefixed with the hostname, so lean.* hits stay distinguishable
from goldenphysics.org's own paths in one dashboard instead of colliding on
identical page paths (e.g. both sites having a "/").
"""
import os, glob

webdir = "blueprint/src/web"

SNIPPET = (
    '<script>window.goatcounter={path:function(p){return location.host+p}}</script>\n'
    '<script data-goatcounter="https://goldenphysics.goatcounter.com/count" '
    'async src="//gc.zgo.at/count.js"></script>\n'
)

files = glob.glob(os.path.join(webdir, "**", "*.html"), recursive=True)
count = 0
for path in files:
    with open(path, "r") as f:
        html = f.read()
    if "goatcounter" in html:
        continue
    if "</body>" in html:
        html = html.replace("</body>", SNIPPET + "</body>", 1)
    else:
        html = html + SNIPPET
    with open(path, "w") as f:
        f.write(html)
    count += 1

print(f"Injected GoatCounter into {count}/{len(files)} HTML files")
