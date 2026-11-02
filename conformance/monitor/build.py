#!/usr/bin/env python3
"""Build compiled-Agda typed Haskell/C libraries and real consumers (no execution).

Run from any directory: python3 conformance/monitor/build.py
Use --check-env PATH when a worktree shares another checkout's pagda environment.
GHC is discovered from PATH or pagda's Agda --with-compiler wrapper, never a fixed
Nix store path. --skip-agda reuses an explicitly supplied --generated directory.
"""
import argparse
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def run(command, env):
    print('+ ' + shlex.join(map(str, command)), flush=True)
    subprocess.run(list(map(str, command)), cwd=ROOT, env=env, check=True)


def toolchain(check_env):
    env = os.environ.copy()
    variables = {}
    if check_env.is_file():
        variables = json.loads(check_env.read_text())['variables']
        env['PATH'] = variables['PATH']['value'] + os.pathsep + env.get('PATH', '')
        for key, entry in variables.items():
            if key.startswith('NIX_') and entry.get('type') == 'exported':
                env[key] = entry['value']
    # This is a local build, not a Nix derivation: local absolute output paths
    # must be accepted by the selected compiler/linker wrappers.
    env['NIX_ENFORCE_PURITY'] = '0'
    ghc = env.get('GHC') or shutil.which('ghc', path=env.get('PATH'))
    if not ghc:
        agda = shutil.which('agda', path=env.get('PATH'))
        if agda:
            try:
                wrapper = Path(agda).read_text()
            except UnicodeError:
                wrapper = ''
            match = re.search(r'--with-compiler=([^\s"\']+)', wrapper)
            if match:
                ghc = match.group(1)
    if not ghc or not Path(ghc).is_file():
        raise SystemExit('GHC not found: set GHC, enter the pagda build environment, or supply --check-env')
    env['PATH'] = str(Path(ghc).parent) + os.pathsep + env.get('PATH', '')
    return ghc, env


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-env', type=Path, default=ROOT / '.pagda/check-env')
    parser.add_argument('--output', type=Path, default=ROOT / '_build/monitor')
    parser.add_argument('--generated', type=Path)
    parser.add_argument('--skip-agda', action='store_true')
    parser.add_argument('--pagda', default=os.environ.get('PAGDA_BIN', 'pagda'))
    args = parser.parse_args()
    out = args.output.resolve()
    generated = (args.generated or out / 'agda').resolve()
    out.mkdir(parents=True, exist_ok=True)
    if not args.skip_agda:
        # --useUntracked false is the repository's canonical pagda policy.
        run([args.pagda, '--useUntracked', 'false', 'check', 'src/Conformance/Wire.agda', '--',
             '--compile', '--no-main', '--ghc-dont-call-ghc', '--compile-dir=' + str(generated),
             '+RTS', '-M3G', '-H1G', '-RTS'], os.environ.copy())
    elif args.generated is None:
        parser.error('--skip-agda requires --generated (no implicit stale binding reuse)')
    ghc, env = toolchain(args.check_env.resolve())
    wire = generated / 'MAlonzo/Code/Conformance/Wire.hs'
    text = wire.read_text()
    names = re.findall(r'^-- Conformance\.Wire\.respond\s*\n(d_respond_\d+)\s*::', text, re.MULTILINE)
    if len(names) != 1:
        raise SystemExit('Expected one concrete Conformance.Wire.respond export; generated ABI changed')
    glue = out / 'private/Passport/Monitor/Generated.hs'
    glue.parent.mkdir(parents=True, exist_ok=True)
    glue.write_text('module Passport.Monitor.Generated (respond) where\n'
                    'import Data.Text (Text)\n'
                    'import qualified MAlonzo.Code.Conformance.Wire as Wire\n'
                    'respond :: (Text -> Text) -> Text -> Text\n'
                    'respond = Wire.' + names[0] + '\n')
    includes = ['-i' + str(HERE), '-i' + str(out / 'private'), '-i' + str(generated)]
    packages = ['-package', 'text', '-package', 'bytestring', '-package', 'containers',
                '-package', 'parsec', '-package', 'deepseq', '-package', 'array', '-package', 'process']
    source = HERE / 'Passport/Monitor/C.hs'
    static = out / 'obj/static'
    dynamic = out / 'obj/dynamic'
    for directory in [static, dynamic]:
        if directory.exists():
            shutil.rmtree(directory)
        directory.mkdir(parents=True, exist_ok=True)
    common = ['-O0', '-threaded', '-fPIC'] + includes + packages
    run([ghc, '--make', '-no-link', *common, '-odir', static, '-hidir', static,
         '-stubdir', static, source], env)
    objects = sorted(static.rglob('*.o'))
    if not objects:
        raise SystemExit('No static monitor objects produced')
    archive = out / 'libpassport_monitor.a'
    # Recreate rather than retaining members from a previous generated closure.
    if archive.exists():
        archive.unlink()
    ar = shutil.which('ar', path=env['PATH'])
    if not ar:
        raise SystemExit('ar missing from selected compiler environment')
    # q preserves distinct module objects even when basenames (e.g. Base.o)
    # coincide; a freshly created archive plus s supplies a full symbol index.
    run([ar, 'qcs', archive, *objects], env)
    shared = out / ('libpassport_monitor.dylib' if sys.platform == 'darwin' else 'libpassport_monitor.so')
    run([ghc, '--make', '-dynamic', '-shared', '-flink-rts', '-no-hs-main', *common,
         '-odir', dynamic, '-hidir', dynamic, '-stubdir', dynamic, '-o', shared, source], env)
    smoke = HERE / 'tests/c_smoke.c'
    # GHC's C driver can leave .o files beside a source even with -odir.
    # Compile each linkage variant with an explicit object output, then link it.
    static_smoke = static / 'c_smoke.o'
    dynamic_smoke = dynamic / 'c_smoke.o'
    run([ghc, '-c', '-fPIC', '-I' + str(HERE), smoke, '-o', static_smoke], env)
    run([ghc, '-c', '-dynamic', '-fPIC', '-I' + str(HERE), smoke, '-o', dynamic_smoke], env)
    run([ghc, '-no-hs-main', '-threaded', *packages,
         static_smoke, archive, '-o', out / 'c-smoke-static'], env)
    run([ghc, '-dynamic', '-no-hs-main', '-threaded', *packages,
         dynamic_smoke, '-L' + str(out), '-lpassport_monitor', '-optl-Wl,-rpath,' + str(out),
         '-o', out / 'c-smoke-shared'], env)
    # Reuse the already compiled static Haskell closure for the typed consumer.
    run([ghc, '--make', *common, '-odir', static, '-hidir', static,
         '-o', out / 'haskell-smoke', HERE / 'tests/HaskellSmoke.hs'], env)
    print('Built static/shared libraries and consumers in ' + str(out))
    print('Run c-smoke-static, c-smoke-shared, and haskell-smoke there after integration.')


if __name__ == '__main__':
    main()
