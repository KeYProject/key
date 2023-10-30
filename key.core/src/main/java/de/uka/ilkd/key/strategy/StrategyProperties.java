/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.Map;
import java.util.Properties;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public final class StrategyProperties extends Properties {

    public static final String INF_FLOW_CHECK_PROPERTY = "INF_FLOW_CHECK_PROPERTY";
    public static final String INF_FLOW_CHECK_TRUE = "INF_FLOW_CHECK_TRUE";
    public static final String INF_FLOW_CHECK_FALSE = "INF_FLOW_CHECK_FALSE";

    public static final String STOPMODE_OPTIONS_KEY = "STOPMODE_OPTIONS_KEY";
    public static final String STOPMODE_DEFAULT = "STOPMODE_DEFAULT";
    public static final String STOPMODE_NONCLOSE = "STOPMODE_NONCLOSE";


    public static final String SPLITTING_OPTIONS_KEY = "SPLITTING_OPTIONS_KEY";
    public static final String SPLITTING_NORMAL = "SPLITTING_NORMAL";
    public static final String SPLITTING_OFF = "SPLITTING_OFF";
    public static final String SPLITTING_DELAYED = "SPLITTING_DELAYED";

    public static final String LOOP_OPTIONS_KEY = "LOOP_OPTIONS_KEY";
    public static final String LOOP_EXPAND = "LOOP_EXPAND";
    public static final String LOOP_EXPAND_BOUNDED = "LOOP_EXPAND_BOUNDED"; // Used for test
                                                                            // generation chrisg
    public static final String LOOP_INVARIANT = "LOOP_INVARIANT";
    public static final String LOOP_SCOPE_INVARIANT = "LOOP_SCOPE_INVARIANT";
    public static final String LOOP_SCOPE_INV_TACLET = "LOOP_SCOPE_INV_TACLET";
    public static final String LOOP_SCOPE_EXPAND = "LOOP_SCOPE_EXPAND";
    public static final String LOOP_NONE = "LOOP_NONE";

    public static final String BLOCK_OPTIONS_KEY = "BLOCK_OPTIONS_KEY";
    public static final String BLOCK_CONTRACT_INTERNAL = "BLOCK_CONTRACT_INTERNAL";
    public static final String BLOCK_CONTRACT_EXTERNAL = "BLOCK_CONTRACT_EXTERNAL";
    public static final String BLOCK_EXPAND = "BLOCK_EXPAND";
    public static final String BLOCK_NONE = "BLOCK_NONE";

    public static final String METHOD_OPTIONS_KEY = "METHOD_OPTIONS_KEY";
    public static final String METHOD_EXPAND = "METHOD_EXPAND";
    public static final String METHOD_CONTRACT = "METHOD_CONTRACT";
    public static final String METHOD_NONE = "METHOD_NONE";

    public static final String MPS_OPTIONS_KEY = "MPS_OPTIONS_KEY";
    public static final String MPS_SKIP = "MPS_SKIP";
    public static final String MPS_MERGE = "MPS_MERGE";
    public static final String MPS_NONE = "MPS_NONE";

    public static final String DEP_OPTIONS_KEY = "DEP_OPTIONS_KEY";
    public static final String DEP_ON = "DEP_ON";
    public static final String DEP_OFF = "DEP_OFF";

    public static final String QUERY_OPTIONS_KEY = "QUERY_NEW_OPTIONS_KEY";
    public static final String QUERY_ON = "QUERY_ON";
    public static final String QUERY_RESTRICTED = "QUERY_RESTRICTED";
    public static final String QUERY_OFF = "QUERY_OFF";

    public static final String QUERYAXIOM_OPTIONS_KEY = "QUERYAXIOM_OPTIONS_KEY";
    public static final String QUERYAXIOM_ON = "QUERYAXIOM_ON";
    public static final String QUERYAXIOM_OFF = "QUERYAXIOM_OFF";

    public static final String NON_LIN_ARITH_OPTIONS_KEY = "NON_LIN_ARITH_OPTIONS_KEY";
    public static final String NON_LIN_ARITH_NONE = "NON_LIN_ARITH_NONE";
    public static final String NON_LIN_ARITH_DEF_OPS = "NON_LIN_ARITH_DEF_OPS";
    public static final String NON_LIN_ARITH_COMPLETION = "NON_LIN_ARITH_COMPLETION";

    public static final String OSS_OPTIONS_KEY = "OSS_OPTIONS_KEY";
    public static final String OSS_ON = "OSS_ON";
    public static final String OSS_OFF = "OSS_OFF";

    public static final String QUANTIFIERS_OPTIONS_KEY = "QUANTIFIERS_OPTIONS_KEY";
    public static final String QUANTIFIERS_NONE = "QUANTIFIERS_NONE";
    public static final String QUANTIFIERS_NON_SPLITTING = "QUANTIFIERS_NON_SPLITTING";
    public static final String QUANTIFIERS_NON_SPLITTING_WITH_PROGS =
        "QUANTIFIERS_NON_SPLITTING_WITH_PROGS";
    public static final String QUANTIFIERS_INSTANTIATE = "QUANTIFIERS_INSTANTIATE";

    public static final String VBT_PHASE = "VBT_PHASE"; // Used for verification-based testing
    public static final String VBT_SYM_EX = "VBT_SYM_EX";
    public static final String VBT_QUAN_INST = "VBT_QUAN_INST";
    public static final String VBT_MODEL_GEN = "VBT_MODEL_GEN";

    public static final String CLASS_AXIOM_OPTIONS_KEY = "CLASS_AXIOM_OPTIONS_KEY";
    public static final String CLASS_AXIOM_OFF = "CLASS_AXIOM_OFF";
    public static final String CLASS_AXIOM_DELAYED = "CLASS_AXIOM_DELAYED";
    public static final String CLASS_AXIOM_FREE = "CLASS_AXIOM_FREE";

    // chrisg
    public static final String AUTO_INDUCTION_OPTIONS_KEY = "AUTO_INDUCTION_OPTIONS_KEY";
    public static final String AUTO_INDUCTION_OFF = "AUTO_INDUCTION_OFF";
    public static final String AUTO_INDUCTION_RESTRICTED = "AUTO_INDUCTION_RESTRICTED";
    public static final String AUTO_INDUCTION_ON = "AUTO_INDUCTION_ON";
    public static final String AUTO_INDUCTION_LEMMA_ON = "AUTO_INDUCTION_LEMMA_ON";

    public static final int USER_TACLETS_NUM = 3;

    public static final String USER_TACLETS_OFF = "USER_TACLETS_OFF";
    public static final String USER_TACLETS_LOW = "USER_TACLETS_LOW";
    public static final String USER_TACLETS_HIGH = "USER_TACLETS_HIGH";

    /**
     * Key used in {@link StrategyProperties} to configure alias checks in a
     * {@code} SymbolicExecutionStrategy}.
     */
    public static final String SYMBOLIC_EXECUTION_ALIAS_CHECK_OPTIONS_KEY =
        "SYMBOLIC_EXECUTION_ALIAS_CHECK_OPTIONS_KEY";

    /**
     * Value of key {@link #SYMBOLIC_EXECUTION_ALIAS_CHECK_OPTIONS_KEY} in
     * {@link StrategyProperties} to disable alias checks in a {@code SymbolicExecutionStrategy}.
     */
    public static final String SYMBOLIC_EXECUTION_ALIAS_CHECK_NEVER =
        "SYMBOLIC_EXECUTION_ALIAS_CHECK_NEVER";

    /**
     * Value of key {@link #SYMBOLIC_EXECUTION_ALIAS_CHECK_OPTIONS_KEY} in
     * {@link StrategyProperties} to enable immediately alias checks in a
     * {@code SymbolicExecutionStrategy}.
     */
    public static final String SYMBOLIC_EXECUTION_ALIAS_CHECK_IMMEDIATELY =
        "SYMBOLIC_EXECUTION_ALIAS_CHECK_IMMEDIATELY";

    /**
     * Key used in {@link StrategyProperties} to avoid branches caused by modalities not part of
     * main execution branch in a {@code SymbolicExecutionStrategy}.
     */
    public static final String SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OPTIONS_KEY =
        "SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OPTIONS_KEY";

    /**
     * Value of key {@link #SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OPTIONS_KEY} in
     * {@link StrategyProperties} to disable branch avoiding caused by modalities not part of main
     * execution in a {@code SymbolicExecutionStrategy}.
     */
    public static final String SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OFF =
        "SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OFF";

    /**
     * Value of key {@link #SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OPTIONS_KEY} in
     * {@link StrategyProperties} to avoid branches caused by modalities not part of main execution
     * by using site proofs in a {@code SymbolicExecutionStrategy}.
     */
    public static final String SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_SIDE_PROOF =
        "SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_SIDE_PROOF";

    private static final long serialVersionUID = -4647245742912258421L;

    /**
     * Section key for storage file to identify strategy settings
     */
    private static final String STRATEGY_PROPERTY = "[StrategyProperty]";

    private static final String USER_TACLETS_OPTIONS_KEY_BASE = "USER_TACLETS_OPTIONS_KEY";


    // String identities.
    private static final String[] STRING_POOL = { INF_FLOW_CHECK_PROPERTY, INF_FLOW_CHECK_TRUE,
        INF_FLOW_CHECK_FALSE, STOPMODE_OPTIONS_KEY, STOPMODE_DEFAULT, STOPMODE_NONCLOSE,
        SPLITTING_OPTIONS_KEY, SPLITTING_NORMAL, SPLITTING_OFF, SPLITTING_DELAYED, LOOP_OPTIONS_KEY,
        LOOP_EXPAND, LOOP_EXPAND_BOUNDED, LOOP_INVARIANT, LOOP_SCOPE_INVARIANT,
        LOOP_SCOPE_INV_TACLET, LOOP_SCOPE_EXPAND, LOOP_NONE, BLOCK_OPTIONS_KEY,
        BLOCK_CONTRACT_INTERNAL, BLOCK_CONTRACT_EXTERNAL, BLOCK_EXPAND, BLOCK_NONE,
        METHOD_OPTIONS_KEY, METHOD_EXPAND, METHOD_CONTRACT, METHOD_NONE, MPS_OPTIONS_KEY, MPS_MERGE,
        MPS_SKIP, MPS_NONE, DEP_OPTIONS_KEY, DEP_ON, DEP_OFF, QUERY_OPTIONS_KEY, QUERY_ON,
        QUERY_RESTRICTED, QUERY_OFF, QUERYAXIOM_OPTIONS_KEY, QUERYAXIOM_ON, QUERYAXIOM_OFF,
        NON_LIN_ARITH_OPTIONS_KEY, NON_LIN_ARITH_NONE, NON_LIN_ARITH_DEF_OPS,
        NON_LIN_ARITH_COMPLETION, OSS_OPTIONS_KEY, OSS_ON, OSS_OFF, QUANTIFIERS_OPTIONS_KEY,
        QUANTIFIERS_NONE, QUANTIFIERS_NON_SPLITTING, QUANTIFIERS_NON_SPLITTING_WITH_PROGS,
        QUANTIFIERS_INSTANTIATE, VBT_PHASE, VBT_SYM_EX, VBT_QUAN_INST, VBT_MODEL_GEN,
        CLASS_AXIOM_OFF, CLASS_AXIOM_DELAYED, CLASS_AXIOM_FREE, AUTO_INDUCTION_OPTIONS_KEY,
        AUTO_INDUCTION_OFF, AUTO_INDUCTION_RESTRICTED, AUTO_INDUCTION_ON, AUTO_INDUCTION_LEMMA_ON,
        USER_TACLETS_OPTIONS_KEY_BASE, USER_TACLETS_OFF, USER_TACLETS_LOW, USER_TACLETS_HIGH,
        userTacletsOptionsKey(1), userTacletsOptionsKey(2), userTacletsOptionsKey(3),
        SYMBOLIC_EXECUTION_ALIAS_CHECK_OPTIONS_KEY, SYMBOLIC_EXECUTION_ALIAS_CHECK_IMMEDIATELY,
        SYMBOLIC_EXECUTION_ALIAS_CHECK_NEVER,
        SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OPTIONS_KEY,
        SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OFF,
        SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_SIDE_PROOF };


    private static final Properties DEFAULT_MAP = new Properties();
    private static final Logger LOGGER = LoggerFactory.getLogger(StrategyProperties.class);

    static {
        DEFAULT_MAP.setProperty(SPLITTING_OPTIONS_KEY, SPLITTING_DELAYED);
        DEFAULT_MAP.setProperty(LOOP_OPTIONS_KEY, LOOP_SCOPE_INV_TACLET);
        DEFAULT_MAP.setProperty(BLOCK_OPTIONS_KEY, BLOCK_CONTRACT_INTERNAL);
        DEFAULT_MAP.setProperty(METHOD_OPTIONS_KEY, METHOD_CONTRACT);
        DEFAULT_MAP.setProperty(MPS_OPTIONS_KEY, MPS_MERGE);
        DEFAULT_MAP.setProperty(OSS_OPTIONS_KEY, OSS_ON);
        DEFAULT_MAP.setProperty(DEP_OPTIONS_KEY, DEP_ON);
        DEFAULT_MAP.setProperty(QUERY_OPTIONS_KEY, QUERY_OFF);
        DEFAULT_MAP.setProperty(QUERYAXIOM_OPTIONS_KEY, QUERYAXIOM_ON);
        DEFAULT_MAP.setProperty(NON_LIN_ARITH_OPTIONS_KEY, NON_LIN_ARITH_NONE);
        DEFAULT_MAP.setProperty(QUANTIFIERS_OPTIONS_KEY, QUANTIFIERS_NON_SPLITTING_WITH_PROGS);
        for (int i = 1; i <= USER_TACLETS_NUM; ++i) {
            DEFAULT_MAP.setProperty(userTacletsOptionsKey(i), USER_TACLETS_OFF);
        }
        DEFAULT_MAP.setProperty(INF_FLOW_CHECK_PROPERTY, INF_FLOW_CHECK_FALSE);
        DEFAULT_MAP.setProperty(STOPMODE_OPTIONS_KEY, STOPMODE_DEFAULT);
        DEFAULT_MAP.setProperty(VBT_PHASE, VBT_SYM_EX);
        DEFAULT_MAP.setProperty(CLASS_AXIOM_OPTIONS_KEY, CLASS_AXIOM_FREE);
        DEFAULT_MAP.setProperty(AUTO_INDUCTION_OPTIONS_KEY, AUTO_INDUCTION_OFF); // chrisg
        DEFAULT_MAP.setProperty(SYMBOLIC_EXECUTION_ALIAS_CHECK_OPTIONS_KEY,
            SYMBOLIC_EXECUTION_ALIAS_CHECK_NEVER);
        DEFAULT_MAP.setProperty(SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OPTIONS_KEY,
            SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OFF);
    }

    public StrategyProperties() {
        put(SPLITTING_OPTIONS_KEY, DEFAULT_MAP.get(SPLITTING_OPTIONS_KEY));
        put(LOOP_OPTIONS_KEY, DEFAULT_MAP.get(LOOP_OPTIONS_KEY));
        put(BLOCK_OPTIONS_KEY, DEFAULT_MAP.get(BLOCK_OPTIONS_KEY));
        put(METHOD_OPTIONS_KEY, DEFAULT_MAP.get(METHOD_OPTIONS_KEY));
        put(MPS_OPTIONS_KEY, DEFAULT_MAP.get(MPS_OPTIONS_KEY));
        put(DEP_OPTIONS_KEY, DEFAULT_MAP.get(DEP_OPTIONS_KEY));
        put(QUERY_OPTIONS_KEY, DEFAULT_MAP.get(QUERY_OPTIONS_KEY));
        put(QUERYAXIOM_OPTIONS_KEY, DEFAULT_MAP.get(QUERYAXIOM_OPTIONS_KEY));
        put(NON_LIN_ARITH_OPTIONS_KEY, DEFAULT_MAP.get(NON_LIN_ARITH_OPTIONS_KEY));
        put(OSS_OPTIONS_KEY, DEFAULT_MAP.get(OSS_OPTIONS_KEY));
        put(QUANTIFIERS_OPTIONS_KEY, DEFAULT_MAP.get(QUANTIFIERS_OPTIONS_KEY));
        for (int i = 1; i <= USER_TACLETS_NUM; ++i) {
            put(userTacletsOptionsKey(i), DEFAULT_MAP.get(userTacletsOptionsKey(i)));
        }
        put(INF_FLOW_CHECK_PROPERTY, DEFAULT_MAP.get(INF_FLOW_CHECK_PROPERTY));
        put(STOPMODE_OPTIONS_KEY, DEFAULT_MAP.get(STOPMODE_OPTIONS_KEY));
        put(VBT_PHASE, DEFAULT_MAP.getProperty(VBT_PHASE));
        put(CLASS_AXIOM_OPTIONS_KEY, DEFAULT_MAP.getProperty(CLASS_AXIOM_OPTIONS_KEY));
        put(AUTO_INDUCTION_OPTIONS_KEY, DEFAULT_MAP.getProperty(AUTO_INDUCTION_OPTIONS_KEY));
    }

    public static String userTacletsOptionsKey(int i) {
        return USER_TACLETS_OPTIONS_KEY_BASE + i;
    }

    public static String getDefaultProperty(String key) {
        return DEFAULT_MAP.getProperty(key);
    }

    public static StrategyProperties read(Properties p) {
        StrategyProperties sp = new StrategyProperties();

        sp.put(SPLITTING_OPTIONS_KEY, readSingleOption(p, SPLITTING_OPTIONS_KEY));
        sp.put(LOOP_OPTIONS_KEY, readSingleOption(p, LOOP_OPTIONS_KEY));
        sp.put(BLOCK_OPTIONS_KEY, readSingleOption(p, BLOCK_OPTIONS_KEY));
        sp.put(METHOD_OPTIONS_KEY, readSingleOption(p, METHOD_OPTIONS_KEY));
        sp.put(MPS_OPTIONS_KEY, readSingleOption(p, MPS_OPTIONS_KEY));
        sp.put(DEP_OPTIONS_KEY, readSingleOption(p, DEP_OPTIONS_KEY));
        sp.put(QUERY_OPTIONS_KEY, readSingleOption(p, QUERY_OPTIONS_KEY));
        sp.put(QUERYAXIOM_OPTIONS_KEY, readSingleOption(p, QUERYAXIOM_OPTIONS_KEY));
        sp.put(NON_LIN_ARITH_OPTIONS_KEY, readSingleOption(p, NON_LIN_ARITH_OPTIONS_KEY));
        sp.put(OSS_OPTIONS_KEY, readSingleOption(p, OSS_OPTIONS_KEY));
        sp.put(QUANTIFIERS_OPTIONS_KEY, readSingleOption(p, QUANTIFIERS_OPTIONS_KEY));
        for (int i = 1; i <= USER_TACLETS_NUM; ++i) {
            sp.put(userTacletsOptionsKey(i), readSingleOption(p, userTacletsOptionsKey(i)));
        }
        sp.put(INF_FLOW_CHECK_PROPERTY, readSingleOption(p, INF_FLOW_CHECK_PROPERTY));
        sp.put(STOPMODE_OPTIONS_KEY, readSingleOption(p, STOPMODE_OPTIONS_KEY));
        sp.put(VBT_PHASE, readSingleOption(p, VBT_PHASE));
        sp.put(CLASS_AXIOM_OPTIONS_KEY, readSingleOption(p, CLASS_AXIOM_OPTIONS_KEY));
        sp.put(AUTO_INDUCTION_OPTIONS_KEY, readSingleOption(p, AUTO_INDUCTION_OPTIONS_KEY));
        sp.put(SYMBOLIC_EXECUTION_ALIAS_CHECK_OPTIONS_KEY,
            readSingleOption(p, SYMBOLIC_EXECUTION_ALIAS_CHECK_OPTIONS_KEY));
        sp.put(SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OPTIONS_KEY,
            readSingleOption(p, SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OPTIONS_KEY));
        return sp;
    }


    /**
     * Sets the default settings for symbolic execution on the given {@link StrategyProperties}.
     *
     * @param sp The {@link StrategyProperties} to modify.
     * @param quantifierInstantiationWithSplitting Instantiate quantifiers?
     * @param methodTreatmentContract Use method contracts or inline method bodies otherwise?
     * @param loopTreatmentInvariant Use loop invariants or unrole loops otherwise?
     * @param blockTreatmentContract Block contracts or expand otherwise?
     * @param nonExecutionBranchHidingSideProofs {@code true} hide non-execution branch labels by
     *        side proofs, {@code false} do not hide execution branch labels.
     * @param aliasChecks Do alias checks?
     */
    public static void setDefaultStrategyProperties(StrategyProperties sp,
            boolean quantifierInstantiationWithSplitting, boolean methodTreatmentContract,
            boolean loopTreatmentInvariant, boolean blockTreatmentContract,
            boolean nonExecutionBranchHidingSideProofs, boolean aliasChecks) {
        // TODO (DS, 2017-05-11): Would be great to also use the loop scope
        // invariant for the SED. For this, one would
        // however have to change the SED's
        // implementation and to update the tests.
        sp.setProperty(StrategyProperties.LOOP_OPTIONS_KEY,
            loopTreatmentInvariant ? StrategyProperties.LOOP_INVARIANT
                    : StrategyProperties.LOOP_EXPAND);
        sp.setProperty(StrategyProperties.BLOCK_OPTIONS_KEY,
            blockTreatmentContract ? StrategyProperties.BLOCK_CONTRACT_INTERNAL
                    : StrategyProperties.BLOCK_EXPAND);
        sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY,
            methodTreatmentContract ? StrategyProperties.METHOD_CONTRACT
                    : StrategyProperties.METHOD_EXPAND);
        sp.setProperty(StrategyProperties.OSS_OPTIONS_KEY, StrategyProperties.OSS_ON);
        sp.setProperty(StrategyProperties.MPS_OPTIONS_KEY, StrategyProperties.MPS_MERGE);
        sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY, StrategyProperties.QUERY_RESTRICTED);
        sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY,
            StrategyProperties.NON_LIN_ARITH_DEF_OPS);
        sp.setProperty(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY,
            StrategyProperties.AUTO_INDUCTION_OFF);
        sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY, StrategyProperties.DEP_OFF);
        sp.setProperty(StrategyProperties.QUERYAXIOM_OPTIONS_KEY, StrategyProperties.QUERYAXIOM_ON);
        sp.setProperty(StrategyProperties.SPLITTING_OPTIONS_KEY,
            StrategyProperties.SPLITTING_DELAYED);
        sp.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY,
            StrategyProperties.STOPMODE_DEFAULT);
        sp.setProperty(StrategyProperties.CLASS_AXIOM_OPTIONS_KEY,
            StrategyProperties.CLASS_AXIOM_FREE);
        sp.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY,
            quantifierInstantiationWithSplitting ? StrategyProperties.QUANTIFIERS_INSTANTIATE
                    : StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS);
        sp.setProperty(StrategyProperties.SYMBOLIC_EXECUTION_ALIAS_CHECK_OPTIONS_KEY,
            aliasChecks ? StrategyProperties.SYMBOLIC_EXECUTION_ALIAS_CHECK_IMMEDIATELY
                    : StrategyProperties.SYMBOLIC_EXECUTION_ALIAS_CHECK_NEVER);
        sp.setProperty(
            StrategyProperties.SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OPTIONS_KEY,
            nonExecutionBranchHidingSideProofs
                    ? StrategyProperties.SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_SIDE_PROOF
                    : StrategyProperties.SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OFF);
    }


    /**
     * @param p
     */
    private static Object readSingleOption(Properties p, String key) {
        String o = (String) p.get(STRATEGY_PROPERTY + key);
        if (o != null) {
            o = getUniqueString(o);
        }
        if (o == null) {
            o = (String) DEFAULT_MAP.get(key);
            // remove this line if always satisfied. add another assignment if not.
            assert o.equals(getUniqueString(o));
        }
        return o;
    }

    /**
     * @param in A keyword from the strategy properties. It must be registered in
     *        <code>stringPool</code>.
     * @return Returns the same string but possibly with a different but unique object identity.
     */
    private static String getUniqueString(String in) {
        for (String id : STRING_POOL) {
            if (id.equals(in)) {
                return id;
            }
        }

        // CAUTION:
        // If you changed something in the settings:Perhaps you need to update
        // the string pool in StrategyProperties.

        LOGGER.error("The string \"{}\" is not registered in the"
            + " string pool of StrategyProperties. Probably you are loading"
            + " properties stored with a different KeY version. This setting"
            + " is ignored, default value is taken!", in);
        return null;
    }


    public String getProperty(String key) {
        String val = super.getProperty(key);
        if (val != null) {
            return val;
        }
        return DEFAULT_MAP.getProperty(key);
    }

    public void write(Properties p) {
        p.put(STRATEGY_PROPERTY + SPLITTING_OPTIONS_KEY, get(SPLITTING_OPTIONS_KEY));
        p.put(STRATEGY_PROPERTY + LOOP_OPTIONS_KEY, get(LOOP_OPTIONS_KEY));
        p.put(STRATEGY_PROPERTY + BLOCK_OPTIONS_KEY, get(BLOCK_OPTIONS_KEY));
        p.put(STRATEGY_PROPERTY + METHOD_OPTIONS_KEY, get(METHOD_OPTIONS_KEY));
        p.put(STRATEGY_PROPERTY + MPS_OPTIONS_KEY, get(MPS_OPTIONS_KEY));
        p.put(STRATEGY_PROPERTY + DEP_OPTIONS_KEY, get(DEP_OPTIONS_KEY));
        p.put(STRATEGY_PROPERTY + QUERY_OPTIONS_KEY, get(QUERY_OPTIONS_KEY));
        p.put(STRATEGY_PROPERTY + QUERYAXIOM_OPTIONS_KEY, get(QUERYAXIOM_OPTIONS_KEY));
        p.put(STRATEGY_PROPERTY + NON_LIN_ARITH_OPTIONS_KEY, get(NON_LIN_ARITH_OPTIONS_KEY));
        p.put(STRATEGY_PROPERTY + OSS_OPTIONS_KEY, get(OSS_OPTIONS_KEY));
        p.put(STRATEGY_PROPERTY + QUANTIFIERS_OPTIONS_KEY, get(QUANTIFIERS_OPTIONS_KEY));
        for (int i = 1; i <= USER_TACLETS_NUM; ++i) {
            p.put(STRATEGY_PROPERTY + userTacletsOptionsKey(i), get(userTacletsOptionsKey(i)));
        }
        p.put(STRATEGY_PROPERTY + INF_FLOW_CHECK_PROPERTY, get(INF_FLOW_CHECK_PROPERTY));
        p.put(STRATEGY_PROPERTY + STOPMODE_OPTIONS_KEY, get(STOPMODE_OPTIONS_KEY));
        p.put(STRATEGY_PROPERTY + VBT_PHASE, get(VBT_PHASE));
        p.put(STRATEGY_PROPERTY + AUTO_INDUCTION_OPTIONS_KEY, get(AUTO_INDUCTION_OPTIONS_KEY));
        p.put(STRATEGY_PROPERTY + CLASS_AXIOM_OPTIONS_KEY, get(CLASS_AXIOM_OPTIONS_KEY));
        Object aliasCheckValue = get(SYMBOLIC_EXECUTION_ALIAS_CHECK_OPTIONS_KEY);
        if (aliasCheckValue != null) {
            p.put(STRATEGY_PROPERTY + SYMBOLIC_EXECUTION_ALIAS_CHECK_OPTIONS_KEY, aliasCheckValue);
        }
        Object avoidBranchingValue =
            get(SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OPTIONS_KEY);
        if (avoidBranchingValue != null) {
            p.put(STRATEGY_PROPERTY + SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OPTIONS_KEY,
                avoidBranchingValue);
        }
    }


    public synchronized Object clone() {
        final Properties p = (Properties) super.clone();
        final StrategyProperties sp = new StrategyProperties();
        sp.putAll(p);
        return sp;
    }


    public boolean isDefault() {
        boolean result = true;
        Set<Map.Entry<Object, Object>> defaults = DEFAULT_MAP.entrySet();
        for (Map.Entry<Object, Object> def : defaults) {
            if (!def.getValue().equals(getProperty((String) def.getKey()))) {
                result = false;
                break;
            }
        }
        return result;
    }
}
