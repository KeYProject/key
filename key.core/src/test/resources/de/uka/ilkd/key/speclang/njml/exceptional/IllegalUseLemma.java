// exceptionClass: SLTranslationException
// msgContains: Invalid lemma call for use_lemma statement (only lemma invocations allowed)
// position: 19/23
// verbose: true
// broken: false

/* If there is no error message, this would close illegally. */

class IllegalUseLemma {
    /*@ model boolean fakeLemma() {
      @   return false;
      @ }
      @*/

    boolean anything;

    /*@ ensures anything; */
    void m() {
        //@ use_lemma fakeLemma();
    }
}
