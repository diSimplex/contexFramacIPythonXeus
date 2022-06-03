# Contex Frama-c IPython-Xeus

A (simple) example of the use of [ConTeXt](https://wiki.contextgarden.net)
to provide [literate ANSI-C
code](https://github.com/stephengaito/literateProgrammingInConTeXt) which
is verified using [Frama-C](https://frama-c.com/) and embedded in a
[Jupytper](https://jupyter.org/)/[IPthon kernel](https://ipython.org/)
([Xeus](https://github.com/jupyter-xeus/xeus)).

## License

This project is Licensed using the Apache 2.0 License (see the
accompanying LICENSE file).

It is based upon heavily refactored code (and Jupyter notebooks) taken
from the original [xeus-calc](https://github.com/jupyter-xeus/xeus-calc)
project on 2022-06-03 at commit
`1a6247de0751cd70e805c758160ae5f04fb343b6`.

The original files were:

- `src/main.cpp`
- `src/xeus_calc_interpreter.cpp`
- `include/xeus-calc/xeus_calc_config.hpp`
- `include/xeus-calc/xeus_calc_interpreter.hpp`
- `share/jupyter/kernels/xcalc/kernel.json.in`
- `notebooks/Xeus-calc.ipynb`

They are being used via the original QuantStack license which can be found
in the accompanying LICENSE-QuantStack file.
