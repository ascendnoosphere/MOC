"""Cache checked local modules by their source imports and pinned Lean dependencies."""
import hashlib
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile

PACKAGE = Path("Lean")
BASE = "b12a57606056f926fe506f353152331293b5364a"
TEMP = Path(os.environ["RUNNER_TEMP"])
GROUP = os.environ["MOC_GROUP"]
TARGETS = [item.lstrip("+") for item in os.environ["MOC_TARGETS"].split()]
OBJECTS = TEMP / "moc-objects"

def source(module):
    return PACKAGE.joinpath(*module.split(".")).with_suffix(".lean")

def modules_and_key():
    baseline = subprocess.check_output(["git", "ls-tree", "-r", BASE, "--", "Lean"], text=True)
    base_blobs = {}
    for row in baseline.splitlines():
        metadata, path = row.split("\t", 1)
        base_blobs[path] = metadata.split()[2]
    local = {}
    affected = {}
    def visit(module):
        if module in local:
            return affected[module]
        path = source(module)
        data = path.read_bytes()
        imports = re.findall(rb"^import[ \t]+(MOC(?:\.\w+)*)", data, re.MULTILINE)
        modified_imports = [visit(i.decode()) for i in imports]
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        affected[module] = blob != base_blobs.get(path.as_posix()) or any(modified_imports)
        local[module] = data
        return affected[module]
    for name in TARGETS:
        visit(name)
    h = hashlib.sha256()
    for filename in ["lean-toolchain", "lake-manifest.json", "lakefile.lean", "lakefile.toml"]:
        path = PACKAGE / filename
        if path.exists():
            h.update(filename.encode() + b"\0" + path.read_bytes() + b"\0")
    for module, data in sorted(local.items()):
        h.update(module.encode() + b"\0" + data + b"\0")
    return sorted(name for name, changed in affected.items() if changed), h.hexdigest()

def main():
    names, key = modules_and_key()
    if sys.argv[1] == "key":
        with open(os.environ["GITHUB_OUTPUT"], "a") as output:
            print("key=" + key, file=output)
        return
    OBJECTS.mkdir(exist_ok=True)
    with tarfile.open(OBJECTS / (GROUP + ".tgz"), "w:gz", compresslevel=1) as output:
        for name in names:
            rel = Path(*name.split("."))
            for subdir in ["lib/lean", "ir"]:
                directory = PACKAGE / ".lake/build" / subdir / rel.parent
                for artifact in sorted(directory.glob(rel.name + ".*")):
                    if artifact.is_file():
                        output.add(artifact, arcname=artifact.as_posix())
    print(f"Collected {len(names)} compiled local modules for {GROUP}.")

if __name__ == "__main__":
    main()
