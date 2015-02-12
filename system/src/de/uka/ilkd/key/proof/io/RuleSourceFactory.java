package de.uka.ilkd.key.proof.io;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.KeYResourceManager;
import java.io.File;
import java.net.URL;

public class RuleSourceFactory {

    private static final String PATH_TO_RULES = "rules/";

    public static RuleSource fromBuildInRule(final String ruleFileName) {
        final URL u = KeYResourceManager.getManager().getResourceFile(Proof.class, PATH_TO_RULES + ruleFileName);
        if (u == null) {
            // a more specific exception type would probably be better
            throw new RuntimeException("Could not find rule file " + PATH_TO_RULES + ruleFileName);
        }
        return new UrlRuleSource(u);
    }

    public static RuleSource initRuleFile(final URL url) {
        return new UrlRuleSource(url);
    }

    public static RuleSource initRuleFile(final File file) {
        return new FileRuleSource(file);
    }
}
