// msgContains: no viable alternative at input 'asignable
// position: 8/23
// broken: true

// This reports "extraneous input '*' expecting RBRACKET" which is not helpful at all.

public class Keytest {
     //@ asignable arr[*];
     public void test(int[] arr) {
     }
}
