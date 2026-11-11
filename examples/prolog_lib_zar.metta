!(import! &self (library lib_zar))
!(import_prolog_functions_from_file_pred "lib/lib_zar.pl" (has_cmdline_args cmdline_arg_count))
!(test (cmdline_arg_count) 0)
