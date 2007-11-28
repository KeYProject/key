// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.gui;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.Properties;

import de.uka.ilkd.key.gui.configuration.Settings;
import de.uka.ilkd.key.gui.configuration.SettingsListener;
import de.uka.ilkd.key.unittest.ModelGenerator;

/** This class encapsulates the information which 
 *  decision procedure should be used.
 */
public class DecisionProcedureSettings implements Settings {


    private static final String DECISION_PROCEDURE      = "[DecisionProcedure]";
    private static final String DECISION_PROCEDURE_FOR_TEST = "[DecisionProcedureForTest]";
    private static final String SMT_BENCHMARK_ARCHIVING = "[DecisionProcedure]SmtBenchmarkArchiving";
    private static final String SMT_ZIP_PROBLEM_DIR     = "[DecisionProcedure]SmtZipProblemDir";
    private static final String SMT_USE_QUANTIFIERS     = "[DecisionProcedure]SmtUseQuantifiers";
    public static final String SIMPLIFY = "SIMPLIFY";
    public static final String ICS = "ICS";
    public static final String CVCLite = "CVCLite";
    public static final String CVC3 = "CVC3";
    public static final String SVC = "SVC";
    public static final String YICES = "YICES";
    public static final String SMT = "Dummy SMT Translation";
    // only used for test generation
    public static final String COGENT = "Cogent";

    private String decision_procedure = SIMPLIFY;
    private String decision_procedure_for_test = COGENT;
    private boolean smt_benchmark_archiving = false;
    private boolean smt_zip_problem_dir = false;
    private boolean smt_use_quantifiers = true;

    private LinkedList listenerList = new LinkedList();


    // getter
    public String getDecisionProcedure() {
        return decision_procedure;
    }
        

    // setter
    public void setDecisionProcedure(String s) {
        if(!s.equals(decision_procedure)) {
            decision_procedure = s;
            fireSettingsChanged();
        }
    }
    
    // getter
    public String getDecisionProcedureForTest() {
        return decision_procedure_for_test;
    }
        

    // setter
    public void setDecisionProcedureForTest(String s) {
        if(!s.equals(decision_procedure_for_test)) {
            decision_procedure_for_test = s;
            fireSettingsChanged();
        }
    }
    
    /** Enables archiving of SMT benchmarks (which were translated from sequents) during execution
     * of SMT compliant external decision procedures  
     * @param b if set to <tt>true</tt>, the benchmarks will be archived
     */
    public void setDoBenchmarkArchiving( boolean b ) {
        smt_benchmark_archiving = b;
        fireSettingsChanged();
    }
    
    /** Enables zipping of archived problem directories during SMT benchmark archiving
     * @param b if set to <tt>true</tt>, the problem dirs will be zipped
     */
    public void setDoZipProblemDir( boolean b ) {
        smt_zip_problem_dir = b;
        fireSettingsChanged();
    }
    
    /** Enables translation of quantified terms during SMT translation
     * @param b if set to <tt>true</tt>, quantifiers will be translated
     */
    public void setUseQuantifier( boolean b ) {
        smt_use_quantifiers = b;
        fireSettingsChanged();
    }
    
    public boolean useSimplifyForTest() {
        return decision_procedure_for_test.equals(SIMPLIFY);
    }
    
    public boolean useCogentForTest() {
        return decision_procedure_for_test.equals(COGENT);
    }
    
    public boolean useSimplify() {
        return decision_procedure.equals(SIMPLIFY);
    }

    public boolean useICS() {
        return decision_procedure.equals(ICS);
    }
    
    public boolean useCVCLite() {
        return decision_procedure.equals(CVCLite);
    }
    
    public boolean useCVC3() {
        return decision_procedure.equals(CVC3);
    }
    
    public boolean useSVC() {
        return decision_procedure.equals(SVC); 
    }
    
    public boolean useYices() {
        return decision_procedure.equals(YICES); 
    }
    
    public boolean useSMT_Translation() {
        return decision_procedure.equals( SMT );
    }
    
    /** @return <tt>true</tt> if SMT benchmark archiving is enabled */
    public boolean doBenchmarkArchiving() {
        return smt_benchmark_archiving;     
    }
    
    /** @return <tt>true</tt> if problem directories will be zipped during SMT benchmark archiving */
    public boolean doZipProblemDir() {
        return smt_zip_problem_dir;
    }
    
    /** @return <tt>true</tt> if quantifiers will be translated in SMT translation */
    public boolean useQuantifiers() {
        return smt_use_quantifiers;
    }


    /** gets a Properties object and has to perform the necessary
     * steps in order to change this object in a way that it
     * represents the stored settings
     */
    public void readSettings(Properties props) {
        String dec_proc_string = 
            props.getProperty(DECISION_PROCEDURE);
        
        if (dec_proc_string==null ||
                dec_proc_string.equals(SIMPLIFY)) 
            decision_procedure = SIMPLIFY;
        else if (dec_proc_string.equals(ICS))
            decision_procedure = ICS;
        else if (dec_proc_string.equals(CVCLite))
            decision_procedure = CVCLite ;
        else if (dec_proc_string.equals(CVC3))
            decision_procedure = CVC3 ;
        else if (dec_proc_string.equals(SVC))
            decision_procedure = SVC ;
        else if (dec_proc_string.equals(YICES))
            decision_procedure = YICES;
        else if (dec_proc_string.equals(SMT))
            decision_procedure = SMT;
        else
            decision_procedure = SIMPLIFY;
        
        String dec_proc_for_test_string = 
            props.getProperty(DECISION_PROCEDURE_FOR_TEST);    
        if (dec_proc_for_test_string==null ||
                dec_proc_for_test_string.equals(SIMPLIFY)) 
            decision_procedure_for_test = SIMPLIFY;
        else  if (dec_proc_for_test_string.equals(COGENT))
            decision_procedure_for_test = COGENT;
        else
            decision_procedure_for_test = SIMPLIFY;
        
        ModelGenerator.decProdForTestGen = useSimplifyForTest() ? 
                ModelGenerator.SIMPLIFY : ModelGenerator.COGENT;
        
        String val = props.getProperty( SMT_BENCHMARK_ARCHIVING );
        if ( val != null ) smt_benchmark_archiving = Boolean.valueOf(val).booleanValue();
        else smt_benchmark_archiving = false;
        
        val = props.getProperty( SMT_ZIP_PROBLEM_DIR );
        if ( val != null ) smt_zip_problem_dir = Boolean.valueOf(val).booleanValue();
        else smt_zip_problem_dir = false;
        
        val = props.getProperty( SMT_USE_QUANTIFIERS );
        if ( val != null ) smt_use_quantifiers = Boolean.valueOf(val).booleanValue();
        else smt_use_quantifiers = true;
    }


    /** implements the method required by the Settings interface. The
     * settings are written to the given Properties object. Only entries of the form 
     * <key> = <value> (,<value>)* are allowed.
     * @param props the Properties object where to write the settings as (key, value) pair
     */
    public void writeSettings(Properties props) {
        props.setProperty(DECISION_PROCEDURE, getDecisionProcedure());
        props.setProperty(DECISION_PROCEDURE_FOR_TEST, getDecisionProcedureForTest());        
        props.setProperty( SMT_BENCHMARK_ARCHIVING, "" + smt_benchmark_archiving );
        props.setProperty( SMT_ZIP_PROBLEM_DIR,     "" + smt_zip_problem_dir );
        props.setProperty( SMT_USE_QUANTIFIERS,      "" + smt_use_quantifiers );
    }

    /** sends the message that the state of this setting has been
     * changed to its registered listeners (not thread-safe)
     */
    protected void fireSettingsChanged() {
        Iterator it = listenerList.iterator();
        while (it.hasNext()) {	    
            ((SettingsListener)it.next()).settingsChanged(new GUIEvent(this));
        }
    }

    /** adds a listener to the settings object 
     * @param l the listener
     */
    public void addSettingsListener(SettingsListener l) {
        listenerList.add(l);
    }

}
