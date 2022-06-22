// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.


MicroMir permission model
Let u/e/s mean uninit/exclusive/shared respectively.

TODO: I'm not convinced we should use this as a standalone language yet,
however it at the very least gives us a way to compute pre- and post-
conditions for MIR statements.

{ ? }                   Kill(p)                     { u p }
{ }                     Nop                         { }
{ e t, u q }            Set(t, q, Mut)              { e q }
{ s t, u q }            Set(t, q, Not)              { s q }
{ e p }                 Move(p, t)                  { u p, e t }
{ e p }                 Duplicate(p, t, Mut)        { e p, e t }
{ s p }                 Duplicate(p, t, Not)        { s p, e t }
{ }                     Constant (t, k)             { e t }
{ }                     NullOp(op, t1)              { e t1 }
{ e t1 }                UnOp(op, t1, t2)            { e t2 }
{ e t1, e t2 }          BinOp(op, flag, t1, t2, t3) { e t3 }
{ m p }                 Len(p, t, Mut)              { e p, e t}
{ s p }                 Len(p, t, Not)              { s p, e t}

encoding MIR Terminators
{ }                     Jump(bb)                    [ (bb, { }) ]
{ e t }                 JumpInt(t, Targets, Mut)    [ (bbx, { e t }), ... ]
{ s t }                 JumpInt(t, Targets, Not)    [ (bbx, { s t }), ... ]

{ e _0 }                Return(Mut)                 [ ]
{ s _0 }                Return(Not)                 [ ]
{ }                     EndVerif                    [ ] & assert False



Question: What do binary operators do to permissions? Can all my Temporary resources be mutable (as they are now)?






WIP: Calls:

 { e/s tf, [e/s ts] }    DoCall(tf, [tis])           { e _0 }    ** These definitely include wand operations too
    tf      := temporary resource for function name
    ts      := temporary resource for arguments
            TODO: Is return place uninitialized before, or after the call? What if it alises an argument?
                    I'm assuming after, but leaving the design open to either (yay microcode flexibility :) )
    For calls that definitely diverge (destination is None) assert False afterwards.
    For calls that do not, move _0 to the destination place, and GOTO the destination block.
{ e _0 }                Return(bb)                  { assert false }






Example translations:

(1)     Assign(_4, Use(Copy(_6.f)))
            (where _6.f is a shared reference to a Copy type)
    ==> { ? }               Kill(_4)                    { u _4 }
        { s _6.f }          Duplicate(_6.f, temp1, mut) { s _6.f, e temp1 }
        { u _4, e temp1 }   Set(_4, temp1, Mut)         { e _4 }

    ==> Preconditions for the whole statment:
            ? (conditions in order to kill _4, computed later)
            s _6.f
         
        Postconditions for the whole statement
            e _4
            s _6.f
    
        Translation can be strengthened into the pre/post conditions for the whole statement
        in a straightfoward way using the frame rule. Note that the pre/post conditions match
        between statements.
        
            { ?, s _6.f }
                Kill(_4)
            { u _4, s _6.f }
                Duplicate(_6.f, temp1, Mut)
            { u _4, s _6.f, e temp1 }
                Set(_4, temp1, Mut)
            { e _4, s _6.f }


(2)     Assign(_2.f, CheckedBinaryOp(Add), Constant(5), Move(_7.g))

    ==> { ? }                   Kill(_2.f)                               { u _2.f }
        { e _7.g }              Move(_7.g, temp1)                        { u _7.g, e temp1 }
        { }                     Constant(5, temp2)                       { e temp2 }
        { e temp1, e temp2 }    BinOp (Add, true, temp1, temp2, temp3)   { e temp3 }
        { e temp3, u _2.f }     Set (temp3, _2.f, Mut)                   { e _2.f }

    ==> Combined translation by framing

            { ?, e _7.g }
                Kill(_2.f)
            { u _2.f, e _7.g }
                Move(_7.g, temp1)
            { u _2.f, u _7.g, e temp1}
                Constant(5, temp2)
            { u _2.f, u _7.g, e temp1, e temp2}
                BinOp (Add, true, temp1, temp2, temp3)
            { u _7.g, u _2.f, e temp3 }
                Set (temp3, _2.f, Mut)
            { u _7.g, e _2.f }




(3)     Call(Copy(_1), Vec<Copy(_2), Move(_3.f), Constant(10_u32)), Some<(_8, bbx)>, _, _, _)
    ==> { e _1 }            Duplicate(_1, tf, Mut)      { e _1, e tf }
        { e _2 }            Move(_2, t0, Mut)           { e t0 }
        { e _3.f }          Move(_3.f, t1, Not)         { e t1 }
        { }                 Constant(10, t2)            { e t2 }
        { e t0, e t1, e t2, e t3 }
                            DoCall(t0, Vec<t1, t2, t3>) { e _0 }

        { ? }               Kill(_8)                    { u _8 }
        { e _0 }            Move(_0, tmp1, Mut)         { u _0, e tmp1 } <-- should this be copy? What happens to _0?
        { u _8, e tmp1}     Set(tmp1, _8)               { e _8 }


    Framing of the whole statement:
            { e _1, e _2, e _3.f }
                Duplicate(_1, tf, Mut)
            { e _1, e _2, e tf, e _3.f }
                Move(_2, t0, Mut)
            { e _1, e t0, e tf, e _3.f }
                Move(_3.f, t1, Not)         
            { e _1, e t0, e tf, e t1 }
                Constant(10, t2)
            { e _1, e t0, e tf, e t1, e t2 }
                Call(t0, Vec<t1, t2, t3>)
            { e _1, e _0 }

            { ?, e _0 }
                Kill(_8)
            { u _8, e _0 }
                Move(_0, tmp1)
            { u _8, u _0, e tmp1 }
                Set(tmp1, _8)
            { u _0, e _8 }




WIP statements (not completely convinced about anything below here yet)
    Q: Exiting the PCS also happens with wands... same underlying mechanic?






Open questions:
    Untranslated MIR statements and RHS cases:
        - (RHS) Repeat
        - (RHS) Ref
        - (RHS) ThreadLocalRef
        - (RHS) AddressOf
        - (RHS) Cast
        - (RHS) Discriminant
        - (RHS) Aggregate
        - (RHS) ShallowInitBox
        - Deinit (Just kill? should it retain the permission u p? Is it always followed by a StorageDead? )
        - CopyNonOverlapping
    AFAIK The following MIR statements do not change the PCS. Do we need them, or can they be special no-ops?
        - FakeRead
        - SetDiscriminant (how is this "used for drop elaboration", again?)
        - Retag (it's for stacked borrows)
        - AscribeUserType (should the type checker have already used this? Is there any dynamic typing?)
        - Coverage
    Where might wands be applied?
        Owned vs borrowed values?
    Can we do our MaybeInit analysis on this?
    Terminators:
        Do we verify unwind paths?





WIP MIR Translations:
    Hesitant because of this issue: https://github.com/rust-lang/rust/issues/68622
    And also this
         > These statements are not required. If the entire MIR body contains no
           StorageLive/StorageDead statements for a particular local, the local is
           always considered live.
    Perhaps we should rely on our own iniaizliation analysis completely,
        and treat these statements as no-ops.
    StorageDead(p)      ->      { ? }       Kill(p)         { u p }
                                { u p }     Exit(p)         { }

    StorageLive(p)      ->      { }         Enter(p)        { u p }
        
        The "enter" microcode op seems a lot like we could just specialize "kill"
        Also, exiting the PCS can have wand-effects.


    The permissions for Repeat:
        If p is shared: always OK,
        If p is exclusive (owned or borrowed) then one of
            - k = 1
            - k = 0
            - p is Clone (this implies p is owned since &mut T is *never* Clone)
        We are not allowed to move out of arrays, values must be copied out.
            - In mut arrays, we're allowed to overwrite the entire array
            - We're also allowed to overwrite individual elements
            - Elements can be read and shared borrowed but not mutably borrowed or moved.

    Repeat(p, k)        ->      { ... p }       ...             { ... tmp1 }    Get the Operand permission, must be copy
                                { e/s tmp1 }    Many(tmp1, l)   { e tmp2 }      Whole array is owned
                                                                                Delegate to unpack????????????
    This needs more thought, and probably a theory for structs with shared fields before
    we can model this operation

