print "digraph interpolation_deps {\n";
# See here for color schemes: https://graphviz.org/doc/info/colors.html
print "  node [shape = ellipse,style=filled,colorscheme = paired12];\n";
print "  subgraph cluster_autosubst { label=\"AutoSubst\" \n}";
while (<>) {
  if (m/.*?theories\/([^\s]*)\.vo.*:(.*)/) {
    $dests = $2 ;
    ($path,$src) = ($1 =~ s/\//\./rg =~ m/(.*\.)?([^.]*)$/);
    if ($path =~ m/AutoSubst\./) {
      print "subgraph cluster_autosubst { \"$path$src\"[label=\"$src\",fillcolor=1]}"
    }else {
      print "\"$path$src\"[label=\"$src\",fillcolor=6,fontcolor=white]"
    }
    for my $dest (split(" ", $dests)) {
      $dest =~ s/\//\./g ;
      print "  \"$1\" -> \"$path$src\";\n" if ($dest =~ m/theories\.(.*)\.vo/);
    }
  }
}
print "}\n";