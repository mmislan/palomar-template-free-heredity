"""Validate a source-only snapshot; optionally replay through a supplied supervisor.

No compiler runs by default. --build requires a JSON array containing the
owner-approved finite resource supervisor command prefix, ending in `--` when
the supervisor needs that delimiter. On the original Windows host the canonical
process_guard public CLI is the required supervisor, not an ad-hoc subprocess.
"""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,sys

def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    replay=ap.add_mutually_exclusive_group()
    replay.add_argument('--build',action='store_true',help='fresh build and standard Linux/bwrap Comparator')
    replay.add_argument('--build-only',action='store_true',help='fresh Solution build under the supplied supervisor')
    ap.add_argument('--supervisor-prefix',type=Path)
    ap.add_argument('--lake',type=Path)
    args=ap.parse_args()
    root=Path(__file__).resolve().parents[1]
    manifest=json.loads((root/'SOURCE_MANIFEST.json').read_text(encoding='utf-8'))
    for row in manifest['files']:
        original=root/row['path']
        p=original.resolve(strict=True)
        if not p.is_relative_to(root) or original.is_symlink():raise RuntimeError('Unsafe source path: '+row['path'])
        if sha(p)!=row['sha256']:raise RuntimeError('Source hash mismatch: '+row['path'])
    toolchain=(root/'lean-toolchain').read_text(encoding='utf-8').strip()
    if toolchain!='leanprover/lean4:v4.35.0-rc2':raise RuntimeError('Unexpected toolchain')
    print('SOURCE_MANIFEST_PASS: '+str(len(manifest['files']))+' files; pinned toolchain preserved')
    if not (args.build or args.build_only):return
    if args.build and os.name=='nt':
        ap.error('The standard Lake Comparator requires Linux/bwrap. Use --build-only for Windows source checking; recorded native comparison used the separately documented adapter.')
    if args.supervisor_prefix is None or args.lake is None:
        ap.error('--build requires --supervisor-prefix and the absolute pinned --lake executable')
    if not args.lake.is_absolute() or not args.lake.is_file():ap.error('--lake must be an existing absolute file')
    prefix=json.loads(args.supervisor_prefix.read_text(encoding='utf-8'))
    if not isinstance(prefix,list) or not prefix or not all(isinstance(x,str) and x for x in prefix):
        ap.error('Supervisor prefix must be a nonempty JSON array of argument strings')
    if os.name=='nt' and not any(Path(x).name=='process_guard.py' for x in prefix):
        ap.error('The original native Windows lane requires the canonical process_guard.py public CLI')
    env=dict(os.environ);env['LEAN_NUM_THREADS']='1'
    commands=[[str(args.lake),'build','Solution']]
    if args.build:commands.append([str(args.lake),'comparator','--config','comparator.json'])
    for command in commands:
        r=subprocess.run(prefix+command,cwd=root,env=env)
        if r.returncode:sys.exit(r.returncode)

if __name__=='__main__':main()
