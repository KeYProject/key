// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy;

import java.util.Properties;


public class StrategyProperties extends Properties {

    public final static String SPLITTING_OPTIONS_KEY = "SPLITTING_OPTIONS_KEY";
    public final static String SPLITTING_NORMAL = "SPLITTING_NORMAL";
    public final static String SPLITTING_OFF = "SPLITTING_OFF";
    public final static String SPLITTING_DELAYED = "SPLITTING_DELAYED";

    public final static String LOOP_OPTIONS_KEY = "LOOP_OPTIONS_KEY";
    public final static String LOOP_EXPAND = "LOOP_EXPAND";
    public final static String LOOP_INVARIANT = "LOOP_INVARIANT";
    public final static String LOOP_NONE = "LOOP_NONE";
    
    public final static String METHOD_OPTIONS_KEY = "METHOD_OPTIONS_KEY";
    public final static String METHOD_EXPAND = "METHOD_EXPAND";
    public final static String METHOD_CONTRACT = "METHOD_CONTRACT";
    public final static String METHOD_NONE = "METHOD_NONE";
    
    public final static String QUERY_OPTIONS_KEY = "QUERY_OPTIONS_KEY";
    public final static String QUERY_EXPAND = "QUERY_EXPAND";
    public final static String QUERY_PROGRAMS_TO_RIGHT = "QUERY_PROGRAMS_TO_RIGHT";
    public final static String QUERY_NONE = "QUERY_NONE";

    public final static String NON_LIN_ARITH_OPTIONS_KEY = "NON_LIN_ARITH_OPTIONS_KEY";
    public final static String NON_LIN_ARITH_NONE = "NON_LIN_ARITH_NONE";
    public final static String NON_LIN_ARITH_DEF_OPS = "NON_LIN_ARITH_DEF_OPS";
    public final static String NON_LIN_ARITH_COMPLETION = "NON_LIN_ARITH_COMPLETION";

    public final static String QUANTIFIERS_OPTIONS_KEY = "QUANTIFIERS_OPTIONS_KEY";
    public final static String QUANTIFIERS_NONE = "QUANTIFIERS_NONE";
    public final static String QUANTIFIERS_NON_SPLITTING = "QUANTIFIERS_NON_SPLITTING";
    public final static String QUANTIFIERS_NON_SPLITTING_WITH_PROGS = "QUANTIFIERS_NON_SPLITTING_WITH_PROGS";
    public final static String QUANTIFIERS_INSTANTIATE = "QUANTIFIERS_INSTANTIATE";
    
    public final static String GOALCHOOSER_OPTIONS_KEY = "GOALCHOOSER_OPTIONS_KEY";
    public final static String GOALCHOOSER_DEFAULT = "GOALCHOOSER_DEFAULT";
    public final static String GOALCHOOSER_DEPTH = "GOALCHOOSER_DEPTH";
    
    public final static String STOPMODE_OPTIONS_KEY = "STOPMODE_OPTIONS_KEY";
    public final static String STOPMODE_DEFAULT = "STOPMODE_DEFAULT";
    public final static String STOPMODE_NONCLOSE = "STOPMODE_NONCLOSE";


    public final static int USER_TACLETS_NUM = 3;
    private final static String USER_TACLETS_OPTIONS_KEY_BASE = "USER_TACLETS_OPTIONS_KEY";
    public static String USER_TACLETS_OPTIONS_KEY(int i)
                             { return USER_TACLETS_OPTIONS_KEY_BASE + i; }
    public final static String USER_TACLETS_OFF = "USER_TACLETS_OFF";
    public final static String USER_TACLETS_LOW = "USER_TACLETS_LOW";
    public final static String USER_TACLETS_HIGH = "USER_TACLETS_HIGH";

    static Properties defaultMap = new Properties();
    
    static {
        defaultMap.setProperty(SPLITTING_OPTIONS_KEY, SPLITTING_DELAYED);
        defaultMap.setProperty(LOOP_OPTIONS_KEY, LOOP_INVARIANT);
        defaultMap.setProperty(METHOD_OPTIONS_KEY, METHOD_EXPAND);
        defaultMap.setProperty(QUERY_OPTIONS_KEY, QUERY_NONE);
        defaultMap.setProperty(NON_LIN_ARITH_OPTIONS_KEY, NON_LIN_ARITH_NONE);
        defaultMap.setProperty(QUANTIFIERS_OPTIONS_KEY, QUANTIFIERS_NON_SPLITTING_WITH_PROGS);
        for (int i = 1; i <= USER_TACLETS_NUM; ++i)
            defaultMap.setProperty(USER_TACLETS_OPTIONS_KEY(i), USER_TACLETS_OFF);
        defaultMap.setProperty(GOALCHOOSER_OPTIONS_KEY, GOALCHOOSER_DEFAULT);
        defaultMap.setProperty(STOPMODE_OPTIONS_KEY, STOPMODE_DEFAULT);
    }
    
    public StrategyProperties() {
        put(SPLITTING_OPTIONS_KEY, defaultMap.get(SPLITTING_OPTIONS_KEY));                
        put(LOOP_OPTIONS_KEY, defaultMap.get(LOOP_OPTIONS_KEY));                
        put(METHOD_OPTIONS_KEY, defaultMap.get(METHOD_OPTIONS_KEY));
        put(QUERY_OPTIONS_KEY, defaultMap.get(QUERY_OPTIONS_KEY));
        put(NON_LIN_ARITH_OPTIONS_KEY, defaultMap.get(NON_LIN_ARITH_OPTIONS_KEY));
        put(QUANTIFIERS_OPTIONS_KEY, defaultMap.get(QUANTIFIERS_OPTIONS_KEY));
        for (int i = 1; i <= USER_TACLETS_NUM; ++i)
            put(USER_TACLETS_OPTIONS_KEY(i), defaultMap.get(USER_TACLETS_OPTIONS_KEY(i)));
        put(GOALCHOOSER_OPTIONS_KEY, defaultMap.get(GOALCHOOSER_OPTIONS_KEY));
        put(STOPMODE_OPTIONS_KEY, defaultMap.get(STOPMODE_OPTIONS_KEY));
    }

    public static String getDefaultProperty(String key) {
        return defaultMap.getProperty(key);
    }
    
    public String getProperty(String key) {
        String val = super.getProperty(key);
        if (val!=null) return val;
        return defaultMap.getProperty(key);
    }
    
    public static StrategyProperties read(Properties p) {        
        StrategyProperties sp = new StrategyProperties();

        sp.put(SPLITTING_OPTIONS_KEY, readSingleOption(p, SPLITTING_OPTIONS_KEY));                
        sp.put(LOOP_OPTIONS_KEY, readSingleOption(p, LOOP_OPTIONS_KEY));                
        sp.put(METHOD_OPTIONS_KEY, readSingleOption(p, METHOD_OPTIONS_KEY));
        sp.put(QUERY_OPTIONS_KEY, readSingleOption(p,QUERY_OPTIONS_KEY));
        sp.put(NON_LIN_ARITH_OPTIONS_KEY, readSingleOption(p,NON_LIN_ARITH_OPTIONS_KEY));
        sp.put(QUANTIFIERS_OPTIONS_KEY, readSingleOption(p,QUANTIFIERS_OPTIONS_KEY));
        for (int i = 1; i <= USER_TACLETS_NUM; ++i)
            sp.put(USER_TACLETS_OPTIONS_KEY(i), readSingleOption(p,USER_TACLETS_OPTIONS_KEY(i)));
        sp.put(GOALCHOOSER_OPTIONS_KEY, readSingleOption(p,GOALCHOOSER_OPTIONS_KEY));
        sp.put(STOPMODE_OPTIONS_KEY, readSingleOption(p,STOPMODE_OPTIONS_KEY));
        return sp;
    }

    /**
     * @param p
     */
    private static Object readSingleOption(Properties p, String key) {
        Object o = (String) p.get("[StrategyProperty]"+key);
        if (o == null) o = defaultMap.get(key);
        return o;
    }

    public void write(Properties p) {                
        p.put("[StrategyProperty]"+SPLITTING_OPTIONS_KEY, get(SPLITTING_OPTIONS_KEY));
        p.put("[StrategyProperty]"+LOOP_OPTIONS_KEY, get(LOOP_OPTIONS_KEY));
        p.put("[StrategyProperty]"+METHOD_OPTIONS_KEY, get(METHOD_OPTIONS_KEY));
        p.put("[StrategyProperty]"+QUERY_OPTIONS_KEY, get(QUERY_OPTIONS_KEY));              
        p.put("[StrategyProperty]"+NON_LIN_ARITH_OPTIONS_KEY, get(NON_LIN_ARITH_OPTIONS_KEY));              
        p.put("[StrategyProperty]"+QUANTIFIERS_OPTIONS_KEY, get(QUANTIFIERS_OPTIONS_KEY));              
        for (int i = 1; i <= USER_TACLETS_NUM; ++i)
            p.put("[StrategyProperty]"+USER_TACLETS_OPTIONS_KEY(i), get(USER_TACLETS_OPTIONS_KEY(i)));
        p.put("[StrategyProperty]"+GOALCHOOSER_OPTIONS_KEY, get(GOALCHOOSER_OPTIONS_KEY));
        p.put("[StrategyProperty]"+STOPMODE_OPTIONS_KEY, get(STOPMODE_OPTIONS_KEY));
    }

    
    public Object clone() {
        final Properties p = (Properties) super.clone();
        final StrategyProperties sp = new StrategyProperties();
        sp.putAll(p);
        return sp;        
    }
    
}
