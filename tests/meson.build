ccComp  = meson.get_compiler('c')

prefix    = get_option('prefix')
prefixInc = prefix / 'include'
prefixLib = prefix / 'lib'

deps = [
  cppComp.find_library('libxeus', dirs: prefixLib),
  cppComp.find_library('libzmq', dirs: prefixLib),
  conda
]

executable(
  'test',
  'main.c',
  link_with: libxcalc,
  dependencies: deps,
  install: true,
)
