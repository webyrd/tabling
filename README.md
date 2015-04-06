Tabling in miniKanren, similar or identical to the implementation described in Part IV of my dissertation: https://github.com/webyrd/dissertation-single-spaced

This code was designed my Ramana Kumar and myself at Indiana University, while working with Dan Friedman.  Ramana implemented the design, which we debugged together.

Please see Section 12.2 of my dissertation for references on tabling.

This implementation has several important (and severe!) limitations:

* the only constraint handled is `==`.  Other constraints, such as `=/=`, `symbolo`, and `absento`, are not supported.

* free logic variables within a tabled goal are not allowed

* the tabling implementation is slow

* the tabling implementation is stateful

* violating any assumption of the tabling implementation is likely to result in incorrect behavior without an error message

Please see my dissertation for more about these limitations, and for a description of the implementation.


You can see the tabling code in use in this miniKanren uncourse hangout, in which we write the code in `konigsberg.scm` and `graph.scm`:

https://www.youtube.com/edit?video_id=AVhDlIFCS0s&video_referrer=watch


To run the tabling tests in Vicare Scheme, please type the following commands at the terminal:

```
> (load "vanilla-r5-minimal.scm")
> (load "tabling-tests.scm")
> (load "tabling-only-tests.scm")
```
