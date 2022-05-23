package de.uka.ilkd.key.proof.init;

/**
 * Java profile for dependences verification
 */
public class JavaDepProfile extends JavaProfile {

    public static final String NAME = "Java with Dependencies Profile";

    public JavaDepProfile() {
        super("standardRules-dependencies.key");
    }

    @Override
    public String name() {
        return NAME;
    }

}
