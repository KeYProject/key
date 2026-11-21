import universe.qual.Rep;
import universe.qual.Peer;
import universe.qual.Dom;
import universe.qual.RepOnly;

/* The following class is not correctly typed w.r.t. the Universe Type System.
 * Each method is supposed to verify the existance of a specific ownership rule. */
public class UniverseFeatures {
    private @Rep Object repField;
    private @Peer Object peerField;
    private @Dom Object domField;

    /*@ normal_behaviour
      @ ensures \dl_owner(o) == this; */
    public void argRep(@Rep Object o) {}

    /*@ normal_behaviour
      @ ensures \dl_owner(\result) == this; */
    public Object fieldRep() {
        return repField;
    }

    /*@ normal_behaviour
      @ ensures \dl_owner(\result) == this; */
    public Object createRep() {
        return new @Rep Object();
    }

    /*@ normal_behaviour
      @ ensures \dl_owner(\result) == this; */
    public Object returnRep() {
        return returnRepAnnot();
    }

    /*@ normal_behaviour
      @ ensures true; */
    public @Rep Object returnRepAnnot() {
        return new Object();
    }

    /*@ normal_behaviour
      @ ensures \dl_owner(o) == \dl_owner(this); */
    public void argPeer(@Peer Object o) {}

    /*@ normal_behaviour
      @ ensures \dl_owner(\result) == \dl_owner(this); */
    public Object fieldPeer() {
        return peerField;
    }

    /*@ normal_behaviour
      @ ensures \dl_owner(\result) == \dl_owner(this); */
    public Object createPeer() {
        return new @Peer Object();
    }

    /*@ normal_behaviour
      @ ensures \dl_owner(\result) == \dl_owner(this); */
    public Object returnPeer() {
        return returnPeerAnnot();
    }

    /*@ normal_behaviour
      @ ensures true; */
    public @Peer Object returnPeerAnnot() {
        return new Object();
    }

    /*@ normal_behaviour
      @ ensures \dl_dominates(this, o); */
    public void argDom(@Dom Object o) {}

    /*@ normal_behaviour
      @ ensures \dl_dominates(this, \result); */
    public Object fieldDom() {
        return domField;
    }

    /*@ normal_behaviour
      @ ensures \dl_dominates(this, \result); */
    public Object createDom() {
        return new @Dom Object();
    }

    /*@ normal_behaviour
      @ ensures \dl_dominates(this, \result); */
    public Object returnDom() {
        return returnDomAnnot();
    }

    /*@ normal_behaviour
      @ ensures true; */
    public @Dom Object returnDomAnnot() {
        return new Object();
    }

    /*@ normal_behaviour
      @ assignable \dl_createdRepfp(this); */
    public void repOnly() {
        repOnlyMethod();
    }

    /*@ normal_behaviour
      @ ensures true; */
    @RepOnly
    public void repOnlyMethod() {}
}
