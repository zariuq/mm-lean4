$( Simple Metamath proof test $)

$c wff |- ( ) -> $.

$( Declare variables $)
$v p q $.

$( Declare variable types $)
wp $f wff p $.
wq $f wff q $.

$( Axiom: implication introduction $)
ax-1 $a |- ( p -> ( q -> p ) ) $.

$( Simple theorem: just cite the axiom $)
th1 $p |- ( p -> ( q -> p ) ) $= wp wq ax-1 $.
