
prefix = get_option('prefix')

confData = configuration_data()
confData.set('CMAKE_INSTALL_PREFIX', prefix)
confData.set('CMAKE_INSTALL_BINDIR', get_option('bindir'))

configure_file(
	input:  'kernel.json.in',
	output: 'kernel.json',
  configuration: confData,
  install: true,
  install_dir: prefix / 'share' / 'jupyter' / 'kernels' / 'xcalc'
)