import bool

meta ⦉

  /- For intuition, think of having the following types in Idealized RedML:

         vtype goal
         vtype proof
         ctype tactic = goal → ^proof

     We define a custom tactical using the type `{{tactic} → tactic}`
  -/

  let mytac = {
    -- Using the braces {} we have opened a thunk

    print "foo! α☆β";

    fun tac →
    « -- inside these brackets, we are using the redtt term notation;
      -- we use the redtt tactic to introduce a sigma type, and then fill
      -- the first cell with the result of calling the user-provided
      -- tactic, and fill the second cell with the redtt term 'tt'.
      (⦉ !tac ⦊, tt)
    »
  }
⦊

-- Now, we can create a pair of booleans by calling the tactic.
def foo : bool × bool =
  ⦉ !mytac -- force the thunk
      { « ff » } -- apply it to a thunk of a tactic which produces the constant 'ff'
  ⦊

-- observe that we get (pair ff tt) as the resulting proof term
meta ⦉ print normalize foo ⦊

