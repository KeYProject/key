//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.decproc;
import java.util.Vector;
import org.apache.log4j.Logger;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.DecisionProcedureSmtAufliaOp;
import de.uka.ilkd.key.proof.decproc.smtlib.Benchmark;
import de.uka.ilkd.key.proof.decproc.smtlib.ConnectiveFormula;
import de.uka.ilkd.key.proof.decproc.smtlib.Formula;
import de.uka.ilkd.key.proof.decproc.smtlib.TruthValueFormula;
import de.uka.ilkd.key.proof.decproc.translation.PreTranslationVisitor;
import de.uka.ilkd.key.proof.decproc.translation.TermTranslationVisitor;

/** This class is responsible for converting a <tt>Sequent</tt> into the language of the SMT logic
 *  (QF_)AUFLIA.
 *  <p>
 *  To translate a given <tt>Sequent</tt>, a new instance of this class must be created with that
 *  <tt>Sequent</tt> and common <tt>Services</tt> as arguments. The translation is done during the
 *  creation process, so the translation result can be fetched by calling the <tt>getBenchmark</tt>
 *  on the newly created <tt>SmtAufliaTranslation</tt> instance. 
 * 
 * @author akuwertz
 * @version 1.5,  11/15/2006  (Added support for type predicates)
 * 
 * @see de.uka.ilkd.key.proof.decproc.smtlib.Benchmark
 */

public class SmtAufliaTranslation {
    
    /* Additional fields */
            
    /** An identifier for the translated <tt>Sequent</tt> as timestamp */ 
    private String proofName = AbstractDecisionProcedure.getCurrentDateString().substring( 0, 20 ).replaceAll("-", "_To_");
    
    /** The Benchmark representing the result of the translation process */
    private Benchmark benchmark;
    
    /** The <tt>TermTranslationVisitor</tt> used to translate <tt>Term</tt>s */
    private final TermTranslationVisitor ttVisitor;
            
    /** A <tt>boolean</tt> to determine whether quantifier should be translated or not */
    private final boolean translateQuantifiers;
                 
    /** Integer constant to identify the antecedent of a sequent */
    private static final int ANTECEDENT = 0;
    /** Integer constant to identify the succedent of a sequent */
    private static final int SUCCEDENT = 1;
    
    /** A <tt>Logger</tt> for logging and debugging of the translation process into SMT syntax */
    private static final Logger logger = Logger.getLogger( SmtAufliaTranslation.class.getName() );    
    // Logger is created hierarchical to inherit configuration and behaviour from parent
    
    private static final char[] legaliseSymbol = new char[255];
    
    
    
    /* Constructor */
    
    /** A constructor which starts the translation a given <tt>Sequent</tt> to SMT AUFLIA syntax.
     * The result can be fetched with the <tt>getBenchmark</tt> method
     * 
     * @param sequent the <tt>Sequent</tt> which shall be translated 
     * @param services the common <tt>Services</tt> of the KeY prover 
     * @param useQuantifiers determines whether quantifiers should be translated or not
     * 
     * @see #getBenchmark()
     */
    public SmtAufliaTranslation( Sequent sequent, Services services, boolean useQuantifiers ) {
        logger.info( "Creating new SmtAufliaTranslation instance... " );
        translateQuantifiers = useQuantifiers;
        ttVisitor = new TermTranslationVisitor( services, useQuantifiers );
        PreTranslationVisitor.setTranslateQuantifers( translateQuantifiers );
        // Initialize all neccessary objects before starting translation!
        benchmark = translate( sequent );  
        benchmark.setLogic( useQuantifiers );
        logger.info( "Translation completed!" );
    }
    
    
    
    /* Public and private methods */
    
    /** Returns the resulting translation of the <tt>Sequent</tt> this class was created with, as a
     * <tt>Benchmark</tt>
     * 
     * @return the <tt>Benchmark</tt> representing the result of the translation process
     */
    public Benchmark getBenchmark() {
        return benchmark;
    }
    
    
    /** Translates the given <tt>Sequent</tt> into SMT AUFLIA input syntax and returns
     * a <tt>Benchmark</tt> representing the translation result.
     * 
     * @param sequent the <tt>Sequent</tt> which should be translated into SMT AUFLIA syntax
     * @return the Benchmark representing the translation result
     */
    private final Benchmark translate( Sequent sequent ) {
        // Create Benchmark
        Benchmark smtTranslation = new Benchmark( proofName );
        
        // Translate semisequents
        logger.info("Starting sequent translation with antecedent..." );
        Formula antecedentSequent = translate( sequent.antecedent(), ANTECEDENT );
        logger.info( "Finished translating antecedent, starting with succedent..." );
        Formula succedentSequent = translate( sequent.succedent(), SUCCEDENT );
        logger.info( "Finished translating succedent!" );
        
        Formula[] helper;
        logger.info( "Retrieving type predicates..." );
        // Assemble type predicates (if existing) by conjunctions
        Vector typePreds = ttVisitor.getCreatedTypePreds();
        Formula typePredFormula = null;
        if ( typePreds.size() > 0 ) {
            logger.info( "Found " + typePreds.size() + " type predicates," +
                         " integrating them into new formula..." );
            typePredFormula = (Formula) typePreds.get( 0 );
            for ( int i = 1; i < typePreds.size(); i++ ) {     
                helper = new Formula[]{ typePredFormula, (Formula) typePreds.get( i ) };
                typePredFormula = new ConnectiveFormula( DecisionProcedureSmtAufliaOp.AND, helper );
            }
        }    
        
        // Assemble type hierarchy predicates (if existing) by conjunctions
        Vector hierarchyPreds = ttVisitor.getHierarchyPreds();
        Formula typeHierarchyFormula = null;
        if ( hierarchyPreds.size() > 0 ) {
            logger.info( "Found " + hierarchyPreds.size() + " type hierarchy predicates," +
                         " integrating them into new formula..." );
            typeHierarchyFormula = (Formula) hierarchyPreds.get( 0 );
            for ( int i = 1; i < hierarchyPreds.size(); i++ ) {     
                helper = new Formula[]{ typeHierarchyFormula, (Formula) hierarchyPreds.get( i ) };
                typeHierarchyFormula = new ConnectiveFormula( DecisionProcedureSmtAufliaOp.AND, 
                                                              helper );
            }
        }
        
        // Assemble final translation formula and negate it!
        if ( typeHierarchyFormula != null ) {
            helper = new Formula[] { typeHierarchyFormula , antecedentSequent };
            antecedentSequent = new ConnectiveFormula( DecisionProcedureSmtAufliaOp.AND, helper );
            logger.info( "Integrated type hierarchy predicate and translation result formula" );
        }
        
        if ( typePredFormula != null ) {
            helper = new Formula[] { typePredFormula , antecedentSequent };
            antecedentSequent = new ConnectiveFormula( DecisionProcedureSmtAufliaOp.AND, helper );
            logger.info( "Integrated type predicate and translation result formula" );
        }
        
        helper = new Formula[]{ antecedentSequent , succedentSequent };
        Formula finalTranslation = new ConnectiveFormula( DecisionProcedureSmtAufliaOp.IMP, helper );
        finalTranslation = new ConnectiveFormula( DecisionProcedureSmtAufliaOp.NOT , 
                                                  new Formula[] { finalTranslation } );
        logger.info( "Constructed and negated resulting formula!" );
        
        
        // Set formula in Benchmark and return
        smtTranslation.setFormula( finalTranslation );
        return smtTranslation;
    }
    
    
    /** Translates the given <tt>Semisequent</tt> into SMT AUFLIA input syntax. The specified
     * <tt>int</tt> thereby indicates if the given <tt>Semisequent</tt> represents an antecedent
     * or a succedent 
     * 
     * @param ss the <tt>Semisequent</tt> which should be translated into SMT AUFLIA syntax
     * @param skolemization a switch for translating the given <tt>Semisequent</tt> as an antecedent
     *        (zero) or as a succedent (one) [The constant fields of this class should be used!]
     * @return a <tt>Formula</tt> (SMT-LIB) representing the translation result
     */
    private final Formula translate( Semisequent ss, int skolemization ) {
        String connective;
        if ( skolemization == ANTECEDENT ) {
            connective = DecisionProcedureSmtAufliaOp.AND;
        } else {
            connective = DecisionProcedureSmtAufliaOp.OR;
        }
        
        // Translate all ConstrainedFormulae contained in this Semisequent
        Vector translations = new Vector( ss.size() );
        for (int i = 0; i < ss.size(); i++) {
            logger.info( "Starting translation of argument formula " + i + " ..." );
            Formula formTranslation = translate( ss.get( i ).formula() );
            logger.info( "Finished translation of argument formula " + i + "!" );
            logger.debug( "Formula: " + ss.get( i ).formula() );
            if ( formTranslation != null ) {
                logger.debug( "was translated into: " + formTranslation );
                translations.add( formTranslation ); 
            } else {
                logger.debug( "...could not be translated, will be ignored!" );
            }  
        }
        logger.info( "All argument formulae of this semisequent have been tranlated! ");
        
        // Assemble the translated Formulae to a new Formula, using the defined connective
        Formula connectedCf = null;
        logger.info( "Starting to assemble the " + translations.size() + " formulae..." );
        if ( translations.size() > 1 ) {
            connectedCf = (Formula) translations.get( 0 );
            logger.debug( "Done with first formula!" );
            for ( int i = 1; i < translations.size(); i++ ) {     
                Formula[] helper = { connectedCf, (Formula) translations.get( i ) };
                connectedCf = new ConnectiveFormula( connective, helper );
                logger.debug( "Integrated " + (i+1) + ". formula!" );
            }
        } else if ( translations.size() == 1 ) {
            connectedCf = (Formula) translations.get( 0 );
            logger.debug( "Done with first formula!" );
        } else if ( translations.size() == 0 ) {
            // if the semisequent is empty, use semantically equivalent constructs
            logger.debug( "Found empty semisequent (after translation), returning constant!" );
            if ( skolemization == ANTECEDENT ) connectedCf = new TruthValueFormula ( true );
            else connectedCf = new TruthValueFormula( false );
        }        
        logger.info( "Assembled all formulae for semisequent!" );
        return connectedCf;      
    }
    
    
    /** Translates the given <tt>Term</tt> into SMT AUFLIA input syntax.<p> 
     * Thereby before doing the real translation, it is checked if the given <tt>Term</tt> can be 
     * translated into SMT AUFLIA syntax.<br>
     * If so, it is translated and an according <tt>Formula</tt> (SMT-LIB) representing the 
     * translation result is returned. If not, <tt>null</tt> is returned 
     * 
     * @param toTranslate the <tt>Term</tt> which should be translated into SMT AUFLIA syntax 
     * @return a <tt>Formula</tt> (SMT-LIB) representing the translation of the given <tt>Term</tt> 
     */
    private final Formula translate( Term toTranslate ) {
            
        PreTranslationVisitor preTranslator = 
            (PreTranslationVisitor) PreTranslationVisitor.getInstance();
        logger.info( "Checking translatability with PreTranslationVisitor..." );
        toTranslate.execPreOrder( preTranslator );
        // No free variables must occur in term toTranslate
        if ( ( (Boolean) preTranslator.getTranslationResult() ).booleanValue() ) {
            if ( preTranslator.noFreeVariableOccurrences( toTranslate ) ) {
                logger.info( "Formula is translatable, executing PostOrderVisitor..." );
                try {
                    toTranslate.execPostOrder( ttVisitor );
                } catch ( RuntimeException e ) {
                    ttVisitor.reset();
                    logger.info( "Visitor failed, skipping current formula", e );
                    logger.debug( "Reseted TermTranslationVisitor!" );
                    throw e;
                    // return null; TODO remove throw (it is only for debugging), uncomment this!
                }
                logger.info( "Visitor completed, fetching result" );
                return (Formula) ttVisitor.getTranslationResult();
            }
        }
        logger.info( "Formula is not translatable!" );
        return null;
    }
    
    
    // Helper functions for identifier translation from KeY names to allowed names in SMT-LIB
    
    /** Converts an arbitrary identifier (as <tt>String</tt>) into a legal SMT-LIB identifier
     * <p>
     * An identifier thereby is legal according to the SMT-LIB specifications, if it contains 
     * letters, digits and '_', '.' or ''' only.<br>
     * The following replacements are done by this method:
     * <ul>
     * <li>Letters and digits remain untouched</li>
     * <li>The characters '_', '.' and ''' also remain untouched</li>
     * <li>The characters '<' and '>' are replaced by '.'</li>
     * <li>All unmentioned characters are replaced by '_'</li>
     * </ul>
     * Further on, all sequences of "_" are replaced by a single "_" character in the end 
     * 
     * @param identifier the identifier to be converted
     * @return a legal identifier according to SMT-LIB specifications, built upon the given 
     *         identifier 
     */
    public static final String legaliseIdentifier( String identifier ) {
        StringBuffer legalIdentifier = new StringBuffer();
        if ( legaliseSymbol[ 'a' ] != 'a' ) initialiseLegalSymbols();
        for( int i = 0; i < identifier.length(); i++ ) {
             legalIdentifier.append( legaliseSymbol[ identifier.charAt( i ) ] );
        }
        return legalIdentifier.toString().replaceAll( "__" , "_" );
    }
    
    
    /** Initialises the static <tt>legaliseSymbol</tt> array */
    private static final void initialiseLegalSymbols() {
        for( int i = 0; i < legaliseSymbol.length; i++ ) legaliseSymbol[i] = '_';
        // Legal symbols
        for( int i = 'a'; i <= 'z'; i++ ) legaliseSymbol[i] = (char) i;
        for( int i = 'A'; i <= 'Z'; i++ ) legaliseSymbol[i] = (char) i;
        for( int i = '0'; i <= '9'; i++ ) legaliseSymbol[i] = (char) i;
        legaliseSymbol['.'] = '.';
        legaliseSymbol['\''] = '\'';
        // Replacements
        legaliseSymbol[':'] = '_';
        legaliseSymbol['<'] = '\'';
        legaliseSymbol['>'] = '\'';   
    }

}
