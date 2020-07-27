# bf4

bf4 is an analysis backend for P4.
It translates P4 code (for the moment V1Model)
into a CFG, performs optimization passes
and then converts it into a verification
condition which is checked using Z3.

## Building bf4

0. Install p4c [prerequisites](../../README.md#Dependencies)
1. Install z3. Currently tested with version 4.8.7
from [official repo](https://github.com/Z3Prover/z3/releases/tag/z3-4.8.7).

2. Install [inja](https://github.com/pantor/inja). Tested
with version [2.2.0](https://github.com/pantor/inja/releases/tag/v2.2.0).
Copy `inja.hpp` to include path (e.g. `/usr/include`)

3. Install [json](https://github.com/nlohmann/json). Tested
with version [3.7.3](https://github.com/nlohmann/json/releases/tag/v3.7.3).
Copy `json.hpp` to include path / nlohmann (e.g. `/usr/include/nlohmann`)

4. Build:
```
mkdir build
cd build
cmake -DENABLE_UNIFIED_COMPILATION=OFF ..
make
make install
```

5. Preprocess
```
cd build/
make cptemplate
python3 ../sigcomm-2020/cleanup_v1.py sample.p4
```

6. Run bf4
```
p4c-analysis sample-integrated.p4
```

7. Making sense of the output (assume output of previous command was redirected to log.txt)

Getting specs:
```
grep -e "WHEN" -e "AND" log.txt
```

Getting fixes:
```
grep -o "missing fixes.*" log.txt | sort -u
```

## Known limitations

- For the moment, bf4 has only limited support for parser loops
(it may not scale well or loop indefinitely)

- Support for automatically adding missing keys is not implemented

- Due to optimzations (e.g. dominator tree) and ssa
conversion some fields/variables may be hard to trace back
in the original program

- In general tracing back things in the original program is far
from ideal