//TODO
// The block contract below is not provable on the exploration branch
// (it works on the master branch).
// I believe this is because some rule that should rename all occurrences of a particular
// program variable only renames those occurrences that do not have a term label attached.
// -- lanzinger
public class Bug {
    
    /*@ normal_behavior
      @ requires idx <= arr.length && idx >= 0;
      @ ensures \result == arr.length - idx;
      @ measured_by arr.length - idx;
      @*/
    public static int lengthFrom(int[] arr, int idx) {
        if (idx == arr.length) {
            return 0;
        } else {
            ++idx;
            /*@ return_behavior
              @ requires arr != null;
              @ requires \old(arr.length - (idx + 1)) == arr.length - idx;
              @ requires \old(arr.length - idx) > 0;
              @ requires idx <= arr.length && idx >= 0;
              @ returns \result == arr.length - idx + 1;
              @ measured_by arr.length - idx;
              @*/
            {
                return lengthFrom(arr, idx) + 1;
            }
        }
    }
}
