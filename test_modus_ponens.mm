$( Test file with modus ponens $)

$c wff |- ( ) -> $.
$v p q r $.

wp $f wff p $.
wq $f wff q $.
wr $f wff r $.

$( Axiom 1: implication introduction $)
ax-1 $a |- ( p -> ( q -> p ) ) $.

$( Axiom 2: distribution $)
ax-2 $a |- ( ( p -> ( q -> r ) ) -> ( ( p -> q ) -> ( p -> r ) ) ) $.

$( Modus ponens $)
ax-mp $a |- ( p -> q ) $.
ax-mp-minor $a |- p $.

$( Prove identity: p -> p $)
${
  id.1 $e |- ( p -> ( ( p -> p ) -> p ) ) $.
  id.2 $e |- ( p -> ( p -> p ) ) $.
  id $p |- ( p -> p ) $=
    wp wp wp id.2 id.1 ax-mp $.
$}
