"""Usage: python3 materialize.py ORIGINAL_SRC PR19_CORE28 OUTPUT_PROOF

Place changes.patch next to this script. The two inputs are the original src/
folder and PR #19's community/fortytwo-phase3-4331/core28/ folder.
"""
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import re
import subprocess
import sys


def checked(path, digest):
    data = path.read_bytes()
    if sha256(data).hexdigest() != digest:
        raise ValueError(f'Source checksum mismatch: {path.name}')
    return data


def materialize(original, winner, output):
    if output.exists():
        raise FileExistsError(f'Output must not already exist: {output}')
    manifest = json.loads(checked(winner / 'verification.json', '64760f1494571260a14000d297520c53a91791c10f6ec7b03b16c8d1a366a238'))
    output.parent.mkdir(parents=True, exist_ok=True)
    with TemporaryDirectory(dir=output.parent) as temp:
        root = Path(temp) / 'proof'
        root.mkdir()
        for name, digest in manifest['pinned_source_files'].items():
            target = root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(checked(original / name, digest))
        root.joinpath('Solution.lean').write_bytes(checked(winner / 'Solution.lean', '03aa0b52f127901667031bcbd1560a5d4d51f6bf5b0a91d1ece403c6fc05cb16'))
        for patch, digest in [(winner / 'changes.patch', 'b6f5156292d405dcac3b77cb5e4f8adca80a9cb617b27c6ea2547f4d1c6593f5'), (Path(__file__).with_name('changes.patch'), '6be61b7b21a76baf0dba2c007acb0ac45a501225b04fedbd89fed01b62fbad26')]:
            # Force paths to be relative to proof/, even if the output is inside a checkout.
            subprocess.run(['patch', '-p1', '-s'], input=checked(patch, digest), cwd=root, check=True)
        sources = {p.relative_to(root): p for p in root.rglob('*.lean')}
        needed = set()
        todo = [Path('Solution.lean')]
        while todo:
            current = todo.pop()
            if current in needed:
                continue
            needed.add(current)
            for name in re.findall(r'^import ([^\s]+)', sources[current].read_text(), re.MULTILINE):
                dep = Path(*name.split('.')).with_suffix('.lean')
                if dep in sources:
                    todo.append(dep)
        for rel in sources.keys() - needed:
            sources[rel].unlink()
        digest = sha256()
        for rel in sorted(needed, key=lambda p: p.as_posix()):
            h = sha256(sources[rel].read_bytes()).hexdigest()
            digest.update(f'{rel.as_posix()} {h}\n'.encode())
        if len(needed) != 147 or digest.hexdigest() != '9167bd7fc14c254ccfb1302333fb1285cabdbf65205d5af09a2c0bccb63d53a7':
            raise ValueError('Unexpected Core 28 proof tree')
        if any(p.is_file() and p.suffix != '.lean' for p in root.rglob('*')):
            raise ValueError('Unexpected non-source output')
        root.rename(output)
        print(f'147 Lean files; SHA-256 {digest.hexdigest()}')


if __name__ == '__main__':
    materialize(*(Path(p).resolve() for p in sys.argv[1:]))
