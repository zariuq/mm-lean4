$( Test database with DUPLICATE FLOAT VARIABLES - should FAIL validation $)

$c class wff $.
$v x y $.

$( First float for x $)
cx $f class x $.

$( INVALID: Second float for x - same variable! $)
cx2 $f class x $.

$( Float for y $)
cy $f class y $.

$( Essential hypothesis $)
h1 $e wff x = y $.

$( Theorem - should have duplicate float for x $)
thm $a wff x = y $.
