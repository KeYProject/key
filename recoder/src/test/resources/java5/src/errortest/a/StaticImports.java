package a;

import static java.lang.System.err;
import static a.Helper.err;
//import static a.Helper.doesnotexist; // compiler error, but recoder ignores this
import static java.lang.System.out;
import static a.Helper.*;


public class StaticImports {
    public void foo() {
        System.out.println(err == null); // ambiguity
        err(); // this should work
        out.println(""); // should work => System.out
        
        PublicMemberClass pumc = new PublicMemberClass();  // ok
        ProtectedMemberClass prmc = new ProtectedMemberClass(); // ok
        PackageMemberClass pamc = new PackageMemberClass();  // ok
        PrivateMemberClass privmc = new PrivateMemberClass(); // fail  

        NonStaticInnerClass nmsic = new NonStaticInnerClass(); // fail
        
        publicInt++;
        protectedInt++;
        privateInt++; // fail
        packageInt++;
        
        publicFoo();
        protectedFoo();
        privateFoo(); // fail
        packageFoo();
    }
}