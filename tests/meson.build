deps = declare_dependency(
        include_directories: [ '..'/'include'],
)

executable(
  'runTests',
  'fcTest.c',
  'test_token.c',
  'main.c',
  dependencies: deps,
  link_with: libxcalc,
)
