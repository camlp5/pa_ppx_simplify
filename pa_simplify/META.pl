#!/usr/bin/env perl

use strict ;
BEGIN { push (@INC, "..") }
use Version ;

our $destdir = shift @ARGV ;

print <<"EOF";
# Specifications for the "pa_ppx_simplify" preprocessor:
version = "$Version::version"
description = "pa_ppx_simplify deriver"

  requires(toploop) = "camlp5,pa_ppx.base,pa_ppx.deriving_plugins.show,hashcons_mlast.runtime"
  archive(toploop) = "pa_simplify.cmo"

    requires(syntax,preprocessor) = "camlp5,pa_ppx.base,pa_ppx.deriving_plugins.show,hashcons_mlast.runtime"
    archive(syntax,preprocessor,-native) = "pa_simplify.cmo"
    archive(syntax,preprocessor,native) = "pa_simplify.cmx"

  package "link" (
  requires(byte) = "camlp5,pa_ppx.base.link,pa_ppx.deriving_plugins.show.link,hashcons_mlast.runtime"
  archive(byte) = "pa_simplify.cmo"
  )
  requires = "camlp5,pa_ppx.base,pa_ppx.deriving_plugins.show,pa_ppx.runtime,hashcons_mlast.runtime"

EOF
