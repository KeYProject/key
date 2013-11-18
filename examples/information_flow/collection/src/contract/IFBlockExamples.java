package contract;

public class IFBlockExamples {
        int low;

        //@ separates low \declassifies l \erases \result;
        public int secure_1(int l) {
            int l1 = l;
            low++;

            int l2 = 7;
            int l3 = 8;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ separates l1;
            {   l1++;
                if(l2 == 8) {}
            }

            return l1;
        }

        //@ separates low \declassifies l \erases \result;
        public int secure_4(int l) {
            int l1 = l;
            low++;

            int l2 = 7;
            int l3 = 8;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ separates l1, l2;
            {   l1 += l2;
            }

            return l1;
        }

        //@ separates low \erases \result;
        public int insecure_1(int l) {
            int l1 = l;
            low++;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ separates l1;
            {   l1++;
            }

            return l1;
        }

        //@ separates \nothing \declassifies l \erases \result;
        public int secure_6(int l) {
            int l1 = l;
            low++;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ separates l1;
            {   l1++;
            }

            return l1;
        }

        //@ separates \nothing \declassifies l \erases \result;
        public int secure_7(int l) {
            low++;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ separates l;
            {   l++;
            }

            return l;
        }

        //@ separates low;
        public int secure_8(int l) {
            low++;

            //@ normal_behavior
            //@ assignable low;
            //@ separates low;
            {   low++;
            }

            return low;
        }


        //@ separates low \declassifies l \erases \result;
        public int secure_2(int l) {
            int l1 = l;
            low++;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ separates l1;
            {   l1++;
                //@ normal_behavior
                //@ assignable \nothing;
                //@ separates l1;
                {   l1++;
                    //@ normal_behavior
                    //@ assignable \nothing;
                    //@ separates l1;
                    {   l1++;
                    }
                }
            }

            return l1;
        }


        //@ separates low \declassifies l \erases \result;
        public int secure_3(int l) {
            int l1 = l;
            low++;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ separates l1;
            {   l1++;
                //@ normal_behavior
                //@ assignable \nothing;
                //@ separates l1;
                {   l1++;
                }
                //@ normal_behavior
                //@ assignable \nothing;
                //@ separates l1;
                {   l1++;
                }
            }

            return l1;
        }

        //@ separates low \declassifies l \erases \result;
        public int insecure_3(int l) {
            int l1 = l;
            low++;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ separates l1;
            {   l1++;
                //@ normal_behavior
                //@ assignable \nothing;
                //@ separates low;
                {   l1++;
                }
                //@ normal_behavior
                //@ assignable \nothing;
                //@ separates l1;
                {   l1++;
                }
            }

            return l1;
        }

        //@ separates low \erases \result;
        public int insecure_4(int l) {
            int l1 = l;
            low++;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ separates l1;
            {   l1++;
                //@ normal_behavior
                //@ assignable \nothing;
                //@ separates l1;
                {   l1++;
                }
                //@ normal_behavior
                //@ assignable \nothing;
                //@ separates l1;
                {   l1++;
                }
            }

            return l1;
        }

        //@ requires l > 0;
        //@ separates low \declassifies l;
        public void block_while_secure(int l) {
            int l1 = low;
            //@ normal_behavior
            //@ assignable \nothing;
            //@ separates l1;
            { l1++;
            }

           /*@
             @ loop_invariant l >= 0;
             @ assignable \nothing;
             @ separates l1, l;
             @ decreases l;
             @*/
            while (l > 0) {
                l--;
                l1++;
            }

            low = l1;
        }


        //@ requires l > 0;
        //@ separates low \declassifies l;
        public void while_block_secure(int l) {
            int l1 = low;
           /*@
             @ loop_invariant l >= 0;
             @ assignable \nothing;
             @ separates l1, l;
             @ decreases l;
             @*/
            while (l > 0) {
                l--;
                l1++;
            }

            //@ normal_behavior
            //@ assignable \nothing;
            //@ separates l1;
            { l1++;
            }

            low = l1;
        }

        //@ requires l > 0;
        //@ separates low \declassifies l;
        public void while_block_insecure(int l) {
            int l1 = low;
           /*@
             @ loop_invariant l >= 0;
             @ assignable \nothing;
             @ separates l;
             @ decreases l;
             @*/
            while (l > 0) {
                l--;
                l1++;
            }

            //@ normal_behavior
            //@ assignable \nothing;
            //@ separates l1;
            { l1++;
            }

            low = l1;
        }

                //@ requires l > 0;
        //@ separates low \declassifies l;
        public void block_no_return_secure(int l) {
            int l1 = low;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ separates l1;
            { l1++;
            }

            low = l1;
        }

        //@ separates low;
        public void secure_5() {
            //@ normal_behavior
            //@ assignable low;
            //@ separates low;
            {   low++;
            }
        }

}
