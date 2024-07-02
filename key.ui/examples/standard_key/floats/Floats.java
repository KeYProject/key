strictfp class Floats {


    float floatField;


    /*@ normal_behaviour 
      @  requires 0f <= floatField <= 1.5f;
      @  ensures 0f <= \result <= 3f;
      @  assignable \strictly_nothing;
      @*/
    float twiceField() {
        return floatField * 2f;
    }

}
