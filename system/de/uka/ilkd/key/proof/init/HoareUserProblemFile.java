package de.uka.ilkd.key.proof.init;

import java.io.File;
import java.io.FileNotFoundException;

import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.parser.*;
import de.uka.ilkd.key.proof.CountingBufferedInputStream;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.util.ExceptionHandlerException;
import de.uka.ilkd.key.util.ProgressMonitor;

public class HoareUserProblemFile extends KeYUserProblemFile {

    public HoareUserProblemFile(String name, File file, ProgressMonitor monitor) {
        super(name, file, monitor);
    }

    public void readProblem(ModStrategy mod) 
    throws ProofInputException {
        if(file == null) return;
        if (initConfig==null) {
            throw new IllegalStateException("KeYUserProblemFile: InitConfig not set.");
        }
        
        try {
            CountingBufferedInputStream cinp = 
                new CountingBufferedInputStream
                    (getNewStream(),monitor,getNumberOfChars()/100);
            DeclPicker lexer = new DeclPicker(new KeYLexer(cinp,initConfig.getServices().getExceptionHandler()));

            final NamespaceSet normal = initConfig.namespaces().copy();
            final NamespaceSet schema = setupSchemaNamespace(normal);
            
            final ParserConfig normalConfig 
                = new ParserConfig(initConfig.getServices(), normal);
            final ParserConfig schemaConfig 
                = new ParserConfig(initConfig.getServices(), schema);
            
            KeYParser problemParser 
                    = new KeYParser(ParserMode.PROBLEM, 
                                    lexer, 
                                    file.toString(), 
                                    schemaConfig, 
                                    normalConfig,
                                    initConfig.getTaclet2Builder(),
                                    initConfig.getTaclets(), 
                                    initConfig.getActivatedChoices()); 
            problemTerm = problemParser.parseProblem();

            if(problemTerm == null) {
                throw new ProofInputException("No \\problem or \\chooseContract in the input file!");
            }

            String[] searchS = {"\\problem", "\\hoare"};         
            
            setProblemHeader(lexer.getText());
            for (int i = 0; i<searchS.length; i++) {
                if(getProblemHeader() != null && 
                        getProblemHeader().lastIndexOf(searchS[i]) != -1){
                    setProblemHeader(getProblemHeader().substring(
                            0, getProblemHeader().lastIndexOf(searchS[i])));
                    break;
                }

            }
            initConfig.setTaclets(problemParser.getTaclets());
            initConfig.add(normalConfig.namespaces(), mod);

            lastParser = problemParser;
        } catch (antlr.ANTLRException e) {
            close();
            throw new ProofInputException(e);
        } catch (FileNotFoundException fnfe) {
            throw new ProofInputException(fnfe);
        } catch (ExceptionHandlerException ehe) {
            close();
            throw ehe;
        }
    }

    public ProofAggregate getPO() {
        
        Sequent seq = Sequent.EMPTY_SEQUENT;
        if (problemTerm.op() == Op.IMP) {
            seq = seq.addFormula(new ConstrainedFormula(problemTerm.sub(0)), true, true).sequent();
            seq = seq.addFormula(new ConstrainedFormula(problemTerm.sub(1)), false, true).sequent();            
        } else {
            seq = seq.addFormula(new ConstrainedFormula(problemTerm), false, true).sequent();
        }        
        return ProofAggregate.createProofAggregate(
                new Proof(name(), seq, getProblemHeader(),
                        initConfig.createTacletIndex(), 
                        initConfig.createBuiltInRuleIndex(),
                        initConfig.getServices(), settings), name());
    }
}
