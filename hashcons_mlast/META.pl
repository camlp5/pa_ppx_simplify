#!/usr/bin/env perl

use strict ;

our $destdir = shift @ARGV ;

print <<"EOF";
# Specifications for "hashcons_mlast"
description = "camlp5 example parsing & quotation support"

package "runtime" (
  directory = "$destdir/hashcons_mlast"
  requires = "hashcons,pa_ppx_q_ast.runtime"
  archive(byte) = "camlp5_ast.cmo camlp5_hashcons.cmo camlp5_migrate.cmo"
  archive(native) = "camlp5_ast.cmx camlp5_hashcons.cmx camlp5_migrate.cmx"
)

package "parser" (
  requires(toploop) = "camlp5,hashcons_mlast.runtime,camlp5.parser_quotations"
  archive(toploop) = "pa_camlp5.cmo"

    requires(syntax,preprocessor) = "camlp5,fmt,hashcons_mlast.runtime,camlp5.parser_quotations"
    archive(syntax,preprocessor,-native) = "pa_camlp5.cmo"
    archive(syntax,preprocessor,native) = "pa_camlp5.cmx"

  package "link" (
  requires(byte) = "camlp5,fmt,hashcons_mlast.runtime,camlp5.parser_quotations.link"
  archive(byte) = "pa_camlp5.cmo"
  )
  requires = "camlp5,fmt,hashcons_mlast.runtime,camlp5.parser_quotations"
)

package "parser_quotations" (
  requires(toploop) = "camlp5,hashcons_mlast.parser"
  archive(toploop) = "q_ast_camlp5.cmo"

    requires(syntax,preprocessor) = "camlp5,fmt,hashcons_mlast.runtime,hashcons_mlast.parser,camlp5.parser_quotations"
    archive(syntax,preprocessor,-native) = "q_ast_camlp5.cmo"
    archive(syntax,preprocessor,native) = "q_ast_camlp5.cmx"

  package "link" (
  requires(byte) = "camlp5,fmt,hashcons_mlast.runtime,hashcons_mlast.parser,camlp5.parser_quotations"
  archive(byte) = "q_ast_camlp5.cmo"
  )
  requires = "camlp5,fmt,hashcons_mlast.runtime,hashcons_mlast.parser,camlp5.parser_quotations"
)

EOF
