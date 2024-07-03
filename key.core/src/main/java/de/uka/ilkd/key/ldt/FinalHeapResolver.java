/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.settings.ProofSettings;

public class FinalHeapResolver {

    private static final ThreadLocal<Boolean> finalEnabledVariable = new ThreadLocal<>();

    public static boolean isFinalEnabled(InitConfig initConfig) {
        ProofSettings settings = initConfig.getSettings();
        if (settings == null) {
            settings = new ProofSettings(ProofSettings.DEFAULT_SETTINGS);
        }
        return isFinalEnabled(settings);
    }

    public static boolean isFinalEnabled(ProofSettings settings) {
        return settings.getChoiceSettings().getDefaultChoices().get("finalFields")
                .equals("finalFields:immutable");
    }

    public static boolean recallIsFinalEnabled() {
        Boolean bool = finalEnabledVariable.get();
        if (bool == null) {
            throw new IllegalStateException("Unset final enabled variable");
        }
        return bool.booleanValue();
    }

    public static void rememberIfFinalEnabled(InitConfig initConfig) {
        finalEnabledVariable.set(isFinalEnabled(initConfig));
    }

    // private final Services services;
    //
    // public FinalHeapResolver(Services services) {
    // this.services = services;
    // }

    // public <T extends Contract> T resolve(T contract) {
    // return (T) contract.map(this::resolve, services);
    // }
    //
    // private Term resolve(Term term) {
    // if (term == null) {
    // // for non-existing clauses in maps.
    // return null;
    // }
    //
    // if(services.getTypeConverter().getHeapLDT().isSelectOp(term.op())) {
    // return resolveSelect(term);
    // }
    //
    // return resolveDefault(term);
    // }
    //
    // private Term resolveDefault(Term term) {
    // Term[] newsubs = null;
    // ImmutableArray<Term> subs = term.subs();
    // for (int i = 0; i < subs.size(); i++) {
    // Term in = subs.get(i);
    // Term out = resolve(in);
    // if (in != out) {
    // if (newsubs == null) {
    // newsubs = subs.toArray(new Term[subs.size()]);
    // }
    // newsubs[i] = out;
    // }
    // }
    //
    // if (newsubs == null) {
    // return term;
    // } else {
    // return services.getTermFactory().createTerm(term.op(), newsubs,
    // term.boundVars(), term.javaBlock(), term.getLabels());
    // }
    // }
    //
    // private Term resolveSelect(Term term) {
    // Term obj = term.sub(1);
    // Term field = term.sub(2);
    // ProgramVariable pv = getFieldSymbol(field);
    // if (pv != null && pv.isFinal()) {
    // return services.getTermBuilder().finalDot(pv.sort(),
    // resolve(obj), field);
    // }
    // return resolveDefault(term);
    // }
    //
    // private ProgramVariable getFieldSymbol(Term fieldTerm) {
    // Operator op = fieldTerm.op();
    // if (op instanceof Function) {
    // final String name = op.name().toString();
    //
    // // check for normal attribute
    // int endOfClassName = name.indexOf("::$");
    //
    // int startAttributeName = endOfClassName + 3;
    //
    //
    // if (endOfClassName < 0) {
    // // not a normal attribute, maybe an implicit attribute like <created>?
    // endOfClassName = name.indexOf("::<");
    // startAttributeName = endOfClassName + 2;
    // }
    //
    // if (endOfClassName < 0) {
    // return null;
    // }
    //
    // final String className = name.substring(0, endOfClassName);
    // final String attributeName = name.substring(startAttributeName);
    //
    // final ProgramVariable attribute =
    // services.getJavaInfo().getAttribute(attributeName, className);
    //
    // return attribute;
    // }
    // return null;
    // }
}
