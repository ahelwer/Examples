"""
Parse all modules in the manifest with SANY.
"""

from argparse import ArgumentParser
from concurrent.futures import ThreadPoolExecutor
import logging
from os import cpu_count
from os.path import dirname, normpath, pathsep
import subprocess
import tla_utils

parser = ArgumentParser(description='Parses all TLA+ modules in the tlaplus/examples repo using SANY.')
parser.add_argument('--tools_jar_path', help='Path to the tla2tools.jar file', required=True)
parser.add_argument('--tlapm_lib_path', help='Path to the TLA+ proof manager module directory; .tla files should be in this directory', required=True)
parser.add_argument('--community_modules_jar_path', help='Path to the CommunityModules-deps.jar file', required=True)
parser.add_argument('--manifest_path', help='Path to the tlaplus/examples manifest.json file', required=True)
parser.add_argument('--skip', nargs='+', help='Space-separated list of .tla modules to skip parsing', required=False, default=[])
parser.add_argument('--only', nargs='+', help='If provided, only parse models in this space-separated list', required=False, default=[])
parser.add_argument('--verbose', help='Set logging output level to debug', action='store_true')
args = parser.parse_args()

logging.basicConfig(level = logging.DEBUG if args.verbose else logging.INFO)

tools_jar_path = normpath(args.tools_jar_path)
tlaps_modules = normpath(args.tlapm_lib_path)
community_modules = normpath(args.community_modules_jar_path)
manifest_path = normpath(args.manifest_path)
examples_root = dirname(manifest_path)
skip_modules = [normpath(path) for path in args.skip]
only_modules = [normpath(path) for path in args.only]

def parse_module(path):
    """
    Parse the given module using SANY.
    """
    logging.info(path)
    # Jar paths must go first
    search_paths = pathsep.join([tools_jar_path, dirname(path), community_modules, tlaps_modules])
    sany = subprocess.run([
        'java',
        '-cp', search_paths,
        'tla2sany.SANY',
        '-error-codes',
        path
    ], capture_output=True)
    output = ' '.join(sany.args) + '\n' + sany.stdout.decode('utf-8')
    if 0 == sany.returncode:
        logging.debug(output)
        return True
    else:
        logging.error(output)
        return False

manifest = tla_utils.load_json(manifest_path)

specs_failing_unicode_parsing = [
    # TLAPS.tla operator null in level-checking
    'specifications/ewd840',
    'specifications/sums_even',
    'specifications/ewd998',
    'specifications/TwoPhase',
    'specifications/byzpaxos',
]

modules_failing_unicode_parsing = [
    # this.operator null in level-checking
    'specifications/SpecifyingSystems/Liveness/LiveHourClock.tla',
    'specifications/SpecifyingSystems/Liveness/MCLiveWriteThroughCache.tla',
    # Unknown operator R
    'specifications/SpecifyingSystems/RealTime/MCRealTime.tla',
    'specifications/SpecifyingSystems/RealTime/MCRealTimeHourClock.tla',
    'specifications/SpecifyingSystems/RealTime/RTMemory.tla',
    'specifications/SpecifyingSystems/RealTime/RTWriteThroughCache.tla',
    'specifications/SpecifyingSystems/RealTime/RealTime.tla',
    # Standard modules
    'specifications/SpecifyingSystems/Standard/Naturals.tla',
    'specifications/SpecifyingSystems/Standard/Integers.tla',
    'specifications/SpecifyingSystems/Standard/Reals.tla',
    'specifications/SpecifyingSystems/Standard/ProtoReals.tla', # root
    'specifications/SpecifyingSystems/Standard/Peano.tla',
    # Level-checking of ASSUME
    'specifications/NanoBlockchain/MCNano.tla',
    'specifications/NanoBlockchain/Nano.tla', # root
    # PlusCal illegal lexeme
    'specifications/byzpaxos/BPConProof.tla',
    'specifications/byzpaxos/Consensus.tla', # root
    'specifications/byzpaxos/PConProof.tla', # root
    'specifications/byzpaxos/VoteProof.tla',
    # TLAPS null operator when level-checking
    'specifications/lamport_mutex/LamportMutex_proofs.tla',
    'specifications/lamport_mutex/NaturalsInduction.tla',
    'specifications/lamport_mutex/SequenceTheorems.tla',
    'specifications/lamport_mutex/WellFoundedInduction.tla',
    'specifications/lamport_mutex/TLAPS.tla', # root
]

# List of all modules to parse and whether they should use TLAPS imports
modules = [
    tla_utils.from_cwd(examples_root, module['path'])
    for spec in manifest['specifications']
    for module in spec['modules']
        if normpath(module['path']) not in skip_modules
        and spec['path'] not in specs_failing_unicode_parsing
        and module['path'] not in modules_failing_unicode_parsing
        and (only_modules == [] or normpath(module['path']) in only_modules)
]

for path in skip_modules:
    logging.info(f'Skipping {path}')

# Parse specs in parallel
thread_count = cpu_count() if not args.verbose else 1
logging.info(f'Parsing using {thread_count} threads')
with ThreadPoolExecutor(thread_count) as executor:
    results = executor.map(parse_module, modules)
    exit(0 if all(results) else 1)

