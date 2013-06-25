/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package object;


/**
 *
 * @author christoph
 */
public class Naumann {
    Node[] m_result;

    /*@ separates   x
          \erases   m_result,
                    (\seq_def int i; 0; m_result.length; m_result[i]),
                    (\seq_def int i; 0; m_result.length; m_result[i].val); */
    //@ helper
    void  Pair_m(int x, int secret) {
        /*@ normal_behavior
            ensures     m_result != null && m_result.length == 10;
            ensures     \typeof(m_result) == \type(Node[]);
            separates       \nothing
              \new_objects  m_result; */
        { m_result = new Node[10]; }
        int i = 0;
        /*@ loop_invariant 0 <= i && i <= m_result.length;
            loop_invariant m_result != null && \typeof(m_result) == \type(Node[]);
            assignable  m_result[*];
            decreases   m_result.length - i;
            separates       i, x,
                            m_result,
                            (\seq_def int j; 0; i; m_result[j]),
                            (\seq_def int j; 0; i; m_result[j].val)
              \new_objects  m_result[i-1];
          @*/
        while (i < 10) {
            m_result[i] = new Node();
            m_result[i].val = x;
            i++;
        }
    }

    class Node {
        public int val;
    }

}
