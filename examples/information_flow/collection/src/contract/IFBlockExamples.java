package contract;

public class IFBlockExamples {
        int low;

        //@ respects low \declassifies l \erases \result;
        public int secure_1(int l) {
            int l1 = l;
            low++;

            int l2 = 7;
            int l3 = 8;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ respects l1;
            {   l1++;
                if(l2 == 8) {}
            }

            return l1;
        }

        //@ respects low \declassifies l \erases \result;
        public int secure_4(int l) {
            int l1 = l;
            low++;

            int l2 = 7;
            int l3 = 8;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ respects l1, l2;
            {   l1 += l2;
            }

            return l1;
        }

        //@ respects low \erases \result;
        public int insecure_1(int l) {
            int l1 = l;
            low++;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ respects l1;
            {   l1++;
            }

            return l1;
        }

        //@ respects \nothing \declassifies l \erases \result;
        public int m(int l) {
            int l1 = l;
            low++;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ respects l1;
            {   l1++;
            }

            return l1;
        }

        //@ respects \nothing \declassifies l \erases \result;
        public int m_1(int l) {
            low++;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ respects l;
            {   l++;
            }

            return l;
        }

        //@ respects low;
        public int m_2(int l) {
            low++;

            //@ normal_behavior
            //@ assignable low;
            //@ respects low;
            {   low++;
            }

            return low;
        }


        //@ respects low \declassifies l \erases \result;
        public int secure_2(int l) {
            int l1 = l;
            low++;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ respects l1;
            {   l1++;
                //@ normal_behavior
                //@ assignable \nothing;
                //@ respects l1;
                {   l1++;
                    //@ normal_behavior
                    //@ assignable \nothing;
                    //@ respects l1;
                    {   l1++;
                    }
                }
            }

            return l1;
        }


        //@ respects low \declassifies l \erases \result;
        public int secure_3(int l) {
            int l1 = l;
            low++;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ respects l1;
            {   l1++;
                //@ normal_behavior
                //@ assignable \nothing;
                //@ respects l1;
                {   l1++;
                }
                //@ normal_behavior
                //@ assignable \nothing;
                //@ respects l1;
                {   l1++;
                }
            }

            return l1;
        }

        //@ respects low \declassifies l \erases \result;
        public int insecure_3(int l) {
            int l1 = l;
            low++;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ respects l1;
            {   l1++;
                //@ normal_behavior
                //@ assignable \nothing;
                //@ respects low;
                {   l1++;
                }
                //@ normal_behavior
                //@ assignable \nothing;
                //@ respects l1;
                {   l1++;
                }
            }

            return l1;
        }

        //@ respects low \erases \result;
        public int insecure_4(int l) {
            int l1 = l;
            low++;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ respects l1;
            {   l1++;
                //@ normal_behavior
                //@ assignable \nothing;
                //@ respects l1;
                {   l1++;
                }
                //@ normal_behavior
                //@ assignable \nothing;
                //@ respects l1;
                {   l1++;
                }
            }

            return l1;
        }

        //@ requires l > 0;
        //@ respects low \declassifies l;
        public void block_while_secure(int l) {
            int l1 = low;
            //@ normal_behavior
            //@ assignable \nothing;
            //@ respects l1;
            { l1++;
            }

           /*@
             @ loop_invariant l >= 0;
             @ assignable \nothing;
             @ respects l1, l;
             @ decreases l;
             @*/
            while (l > 0) {
                l--;
                l1++;
            }

            low = l1;
        }


        //@ requires l > 0;
        //@ respects low \declassifies l;
        public void while_block_secure(int l) {
            int l1 = low;
           /*@
             @ loop_invariant l >= 0;
             @ assignable \nothing;
             @ respects l1, l;
             @ decreases l;
             @*/
            while (l > 0) {
                l--;
                l1++;
            }

            //@ normal_behavior
            //@ assignable \nothing;
            //@ respects l1;
            { l1++;
            }

            low = l1;
        }

        //@ requires l > 0;
        //@ respects low \declassifies l;
        public void while_block_insecure(int l) {
            int l1 = low;
           /*@
             @ loop_invariant l >= 0;
             @ assignable \nothing;
             @ respects l;
             @ decreases l;
             @*/
            while (l > 0) {
                l--;
                l1++;
            }

            //@ normal_behavior
            //@ assignable \nothing;
            //@ respects l1;
            { l1++;
            }

            low = l1;
        }

                //@ requires l > 0;
        //@ respects low \declassifies l;
        public void block_no_return_secure(int l) {
            int l1 = low;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ respects l1;
            { l1++;
            }

            low = l1;
        }

        //@ respects low;
        public void secure_5() {
            //@ normal_behavior
            //@ assignable low;
            //@ respects low;
            {   low++;
            }
        }

}
