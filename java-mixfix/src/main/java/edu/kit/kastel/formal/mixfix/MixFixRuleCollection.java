/*
 * Copyright (C) 2010 Universitaet Karlsruhe, Germany
 *    written by Mattias Ulbrich
 * 
 * The system is protected by the GNU General Public License. 
 * See LICENSE.TXT for details.
 */
package edu.kit.kastel.formal.mixfix;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;


/**
 * This class serves as a collection of rules used by a {@link MixFixParser}.
 * 
 * <p>
 * There two kind of rules:
 * <dl>
 * <dt>left-denotation rules (LED)</dt>
 * <dd>rule which expect a left hand side argument already parsed in the context
 * when given control. They are also called left-recursive and represent the set
 * of rules which - represented as a production - begin with a non terminal
 * symbol</dd>
 * <dt>null-denotation rule (NUD)</dt>
 * <dd>rules which parse their first token from the stream themselves and do not
 * use/rely on a result present in the context. They correspond - represented as
 * productions - to those production which start with a terminal symbol.
 * </dl>
 * 
 * There is only one generic method {@link #addRule(MixFixRule)} which uses the
 * query {@link MixFixRule#isLeftRecursive()} to categorise an added rule. Rules
 * can be retrieved using either {@link #getLEDRules()} or
 * {@link #getNUDRules()}.
 */
public class MixFixRuleCollection<R, T> {

    /**
     * The internal collection of left denotation rules. monotonously growing.
     */
    private List<MixFixRule<R, T>> ledRules = new ArrayList<MixFixRule<R, T>>();

    /**
     * The internal collection of null denotation rules. monotonously growing.
     */
    private List<MixFixRule<R, T>> nudRules = new ArrayList<MixFixRule<R, T>>();

    /**
     * Gets the set of left denotation rules of this collection.
     * 
     * @return an immutable list of rules, not null
     */
    public List<MixFixRule<R, T>> getLEDRules() {
        return Collections.unmodifiableList(ledRules);
    }

    /**
     * Gets the set of null denotation rules of this collection.
     * 
     * @return an immutable list of rules, not null
     */
    public List<MixFixRule<R, T>> getNUDRules() {
        return Collections.unmodifiableList(nudRules);
    }

    /**
     * Adds a rule to the collection
     * 
     * @param rule
     *            the rule to add, not null
     */
    public void addRule(MixFixRule<R, T> rule) {
        if (rule.isLeftRecursive())
            ledRules.add(rule);
        else
            nudRules.add(rule);
    }
}
