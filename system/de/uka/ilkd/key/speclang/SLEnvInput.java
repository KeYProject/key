// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import java.awt.BorderLayout;
import java.awt.Container;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Set;

import javax.swing.*;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.configuration.GeneralSettings;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.recoderext.ConstructorNormalformBuilder;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.JavaASTCollector;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.AbstractEnvInput;
import de.uka.ilkd.key.proof.init.ModStrategy;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.jml.JMLSpecExtractor;
import de.uka.ilkd.key.speclang.ocl.OCLSpecExtractor;


/** 
 * EnvInput for standalone specification language front ends.
 */
public final class SLEnvInput extends AbstractEnvInput {
    
    private static final String INIT_NAME 
    	= ConstructorNormalformBuilder.CONSTRUCTOR_NORMALFORM_IDENTIFIER;
    private static final TermBuilder TB = TermBuilder.DF;
    
        
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    private static String getLanguage() {
        GeneralSettings gs 
            = ProofSettings.DEFAULT_SETTINGS.getGeneralSettings();
        if(gs.useJML() && gs.useOCL()) {
            return "JML/OCL";
        } else if(gs.useJML()) {
            return "JML";
        } else if(gs.useOCL()) {
            return "OCL";
        } else {
            return "no";
        }
    }
    
    
    public SLEnvInput(String javaPath) {
        super(getLanguage() + " specifications", javaPath);
        assert javaPath != null;
    }
    

    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private KeYJavaType[] sortKJTs(KeYJavaType[] kjts) {
        
        Arrays.sort(kjts, new Comparator<KeYJavaType> () {
            public int compare(KeYJavaType o1, KeYJavaType o2) {
                return o1.getFullName().compareTo(o2.getFullName());
            }
        });
        
        return kjts;
    }
    
    
    private ProgramMethod[] sortPMs(ProgramMethod[] pms) {
        Arrays.sort(pms, new Comparator<ProgramMethod> () {
            public int compare(ProgramMethod o1, ProgramMethod o2) {
        	int res = o1.getFullName().compareTo(o2.getFullName());
        	if(res == 0) {
        	    res = o1.getParameterDeclarationCount() 
        	          - o2.getParameterDeclarationCount();
        	}
        	if(res == 0) {
        	    for(int i = 0, n = o1.getParameterDeclarationCount(); i < n; i++) {
        		final KeYJavaType kjt1 = o1.getParameterType(i);
        		final KeYJavaType kjt2 = o2.getParameterType(i);
        		res = kjt1.getFullName().compareTo(kjt2.getFullName());
        		if(res != 0) {
        		    break;
        		}
        	    }
        	}
        	return res;
            }
        });
        
        return pms;
    }    
    
    
    private void showWarningDialog(ImmutableSet<PositionedString> warnings) {
        if(!Main.isVisibleMode()) {
            return;
        }
                
        final JDialog dialog = new JDialog(Main.getInstance(), 
                                           getLanguage() + " warning", 
                                           true);
        dialog.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
        Container pane = dialog.getContentPane();
        pane.setLayout(new BorderLayout());
        
        //top label
        JLabel label = new JLabel("The following non-fatal "
                                  + "problems occurred when translating your " 
                                  + getLanguage() + " specifications:");
        label.setBorder(BorderFactory.createEmptyBorder(5, 5, 0, 5));
        pane.add(label, BorderLayout.NORTH);
          
        //scrollable warning list
        JScrollPane scrollpane = new JScrollPane();
        scrollpane.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
        JList list = new JList(warnings.toArray(new PositionedString[warnings.size()]));
        list.setBorder(BorderFactory.createLoweredBevelBorder());
        scrollpane.setViewportView(list);
        pane.add(scrollpane, BorderLayout.CENTER);
    
        //ok button
        final JButton button = new JButton("OK");
        button.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                dialog.setVisible(false);
                dialog.dispose();
            }
        });
        Dimension buttonDim = new Dimension(100, 27);
        button.setPreferredSize(buttonDim);
        button.setMinimumSize(buttonDim);
        JPanel panel = new JPanel();
        panel.add(button);
        pane.add(panel, BorderLayout.SOUTH);
        dialog.getRootPane().setDefaultButton(button);
        
        button.registerKeyboardAction(
            new ActionListener() {
                public void actionPerformed(ActionEvent event) {
                    if(event.getActionCommand().equals("ESC")) {
                        button.doClick();
                    }
                }
            },
            "ESC",
            KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0),
            JComponent.WHEN_IN_FOCUSED_WINDOW);
        
        dialog.setSize(700, 300);
        dialog.setLocationRelativeTo(Main.getInstance());
        dialog.setVisible(true);
    }
    
    
    /**
     * Converts a contract for a constructor into a contract for <init>.
     */
    private OperationContract transformConstructorContract(
	    					OperationContract contract,
	    					Services services) {
	final JavaInfo javaInfo = services.getJavaInfo();
	final ProgramMethod pm = contract.getProgramMethod();
	final KeYJavaType kjt = pm.getContainerType();
	assert pm.isConstructor();

	//determine corresponding <init> method
	ImmutableList<KeYJavaType> sig = ImmutableSLList.<KeYJavaType>nil();
	for(int i = 0, n = pm.getParameterDeclarationCount(); i < n; i++) {
	    sig = sig.append(pm.getParameterType(i));
	}
	final ProgramMethod initMethod = javaInfo.getProgramMethod(kjt, 
							           INIT_NAME, 
							           sig, 
							           kjt);
	assert initMethod != null;
	
	//collect all fields of current class and its superclasses
	ImmutableList<KeYJavaType> sups = services.getJavaInfo().getAllSupertypes(kjt);
	ImmutableList<Field> fields = ImmutableSLList.<Field>nil();	
	for(KeYJavaType sup : sups) {
	    if(!(sup.getJavaType() instanceof ClassDeclaration)) {
		continue;
	    }
	    fields = fields.prepend(javaInfo.getAllFields(
		    			(ClassDeclaration) sup.getJavaType()));
	}
	
	//build precondition corresponding to <prepare> (including superclasses)	
	Term implicitPre = TB.tt();
	LogicVariable selfVar = new LogicVariable(new Name("self"), 
		                                  kjt.getSort());
	Term selfTerm = TB.var(selfVar);
	for(Field f : fields) {
	    ProgramVariable pv = (ProgramVariable) f.getProgramVariable();
	    if(pv.isImplicit() || pv.isStatic()) {
		continue;
	    }
	    Term defaultValue 
	    	= services.getTypeConverter()
	                  .convertToLogicElement(f.getType().getDefaultValue());
	    Term fieldHasDefaultValue = TB.equals(TB.dot(selfTerm, pv), 
		                                  defaultValue);
	    implicitPre = TB.and(implicitPre, fieldHasDefaultValue);
	}

	return contract.replaceProgramMethod(initMethod, services)
	               .addPre(new FormulaWithAxioms(implicitPre), 
	        	       selfVar, 
	        	       null, 
	        	       services);
    }
    
    
    
    private ImmutableSet<OperationContract> transformConstructorContracts(
	    				ImmutableSet<OperationContract> contracts,
	    				Services services) {
	ImmutableSet<OperationContract> result = DefaultImmutableSet.<OperationContract>nil();
	for(OperationContract contract : contracts) {
	    result = result.add(transformConstructorContract(contract, 
		    					     services));
	}
	return result;
    }
    
    
    private void createSpecs(SpecExtractor specExtractor) 
            throws ProofInputException {
        JavaInfo javaInfo 
            = initConfig.getServices().getJavaInfo();
        SpecificationRepository specRepos 
            = initConfig.getServices().getSpecificationRepository();
       
        //sort types alphabetically (necessary for deterministic names)
        final Set<KeYJavaType> allKeYJavaTypes = javaInfo.getAllKeYJavaTypes();
        final KeYJavaType[] kjts = 
            sortKJTs(allKeYJavaTypes.toArray(new KeYJavaType[allKeYJavaTypes.size()]));
        
        //create specifications for all types
        for(KeYJavaType kjt : kjts) {
            if(!(kjt.getJavaType() instanceof ClassDeclaration 
        	  || kjt.getJavaType() instanceof InterfaceDeclaration)) {
        	continue;
            }
            
            //class invariants
            specRepos.addClassInvariants(
                        specExtractor.extractClassInvariants(kjt));

            //contracts, loop invariants
            final ImmutableList<ProgramMethod> allPMs 
        	= javaInfo.getAllProgramMethodsLocallyDeclared(kjt);
            final ProgramMethod[] pms  //sort methods alphabetically
        	= sortPMs(allPMs.toArray(new ProgramMethod[allPMs.size()]));            
            for(ProgramMethod pm : pms) {
                //contracts
                specRepos.addOperationContracts(
                            specExtractor.extractOperationContracts(pm));
                
                //loop invariants
                JavaASTCollector collector 
                    = new JavaASTCollector(pm.getBody(), LoopStatement.class);
                collector.start();
                for(ProgramElement loop : collector.getNodes()) {
                    LoopInvariant inv = specExtractor.extractLoopInvariant(
                	    			pm, 
                        			(LoopStatement) loop);
                    if(inv != null) {
                        specRepos.setLoopInvariant(inv);
                    }
                }
            }
            
            //constructor contracts (add implicit preconditions, 
            //move to <init> method)
            final ImmutableList<ProgramMethod> allConstructors 
            	= javaInfo.getConstructors(kjt);
            final ProgramMethod[] constructors //sort constructors alphabetically
            	= sortPMs(allConstructors.toArray(
            			new ProgramMethod[allConstructors.size()]));
            for(ProgramMethod constructor : constructors) {
        	assert constructor.isConstructor();
        	ImmutableSet<OperationContract> contracts 
			= specExtractor.extractOperationContracts(constructor);
        	contracts = transformConstructorContracts(
        					contracts, 
        					initConfig.getServices());
        	specRepos.addOperationContracts(contracts);
            }
        }
        
        //show warnings to user
        ImmutableSet<PositionedString> warnings = specExtractor.getWarnings();
        if(warnings != null && warnings.size() > 0) {
            showWarningDialog(warnings);
        }
    }

    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    public void read(ModStrategy mod) throws ProofInputException {
        if(initConfig == null) {
            throw new IllegalStateException("InitConfig not set.");
        }
        
        GeneralSettings gs 
            = ProofSettings.DEFAULT_SETTINGS.getGeneralSettings();
        if(gs.useJML()) {
            createSpecs(new JMLSpecExtractor(initConfig.getServices()));
        }
        if(gs.useOCL()) {
            createSpecs(new OCLSpecExtractor(initConfig.getServices()));
        }
    }
}
