------------------------------ MODULE Simple ------------------------------

EXTENDS Naturals
CONSTANTS Foo, Max

VARIABLES bar

Init == IF Foo
        THEN bar = 0
        ELSE bar = 1

Next == IF bar + 2 =< Max
        THEN bar' = bar + 2
        ELSE UNCHANGED <<bar>>
    
IsEven == bar % 2 = 0
Inv == IF Foo THEN IsEven ELSE ~IsEven

=============================================================================
