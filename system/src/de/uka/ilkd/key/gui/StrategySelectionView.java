// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 



package de.uka.ilkd.key.gui;

import java.awt.Component;
import java.awt.Container;
import java.awt.Dimension;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.ButtonGroup;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JRadioButton;
import javax.swing.JScrollPane;
import javax.swing.ScrollPaneConstants;
import javax.swing.border.Border;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.JavaCardDLStrategy;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;


public final class StrategySelectionView extends JPanel {
    
    private static final long serialVersionUID = -2808575255579411116L;

    private static final String JAVACARDDL_STRATEGY_NAME 
    	= "JavaCardDLStrategy";

    private Map<String, JRadioButton> buttonHashmap = new LinkedHashMap<String, JRadioButton>();
    

   
    private ButtonGroup stratGroup = new ButtonGroup();
    private ButtonGroup splittingGroup = new ButtonGroup();
    private ButtonGroup loopGroup = new ButtonGroup();
    private ButtonGroup blockGroup = new ButtonGroup();
    private ButtonGroup methodGroup = new ButtonGroup();
    private ButtonGroup depGroup = new ButtonGroup();
    private ButtonGroup queryGroup = new ButtonGroup();
    private ButtonGroup queryAxiomGroup = new ButtonGroup();
    private ButtonGroup nonLinArithGroup = new ButtonGroup();
    private ButtonGroup quantifierGroup = new ButtonGroup();
    private ButtonGroup stopModeGroup = new ButtonGroup();
    private ButtonGroup retreatModeGroup = new ButtonGroup();
    private ButtonGroup autoInductionGroup = new ButtonGroup();     
    private ButtonGroup[] userTacletsGroup = new ButtonGroup[StrategyProperties.USER_TACLETS_NUM];
    {
        for (int i = 0; i < StrategyProperties.USER_TACLETS_NUM; ++i)
            userTacletsGroup[i] = new ButtonGroup ();
    }
    private JRadioButton rdBut9;
    private JRadioButton rdBut10;
    private JRadioButton rdBut11;
    private JRadioButton rdBut12;
    private JRadioButton rdBut13;
    private JRadioButton rdBut14;
    private JRadioButton rdBut17;
    private JRadioButton rdBut18;
    private JRadioButton blockContractRadioButton;
    private JRadioButton blockExpandRadioButton;
    //JRadioButton blockNoneRadioButton;
    private JRadioButton noRetreat;
    private JRadioButton retreat;
    private JRadioButton splittingNormal;
    private JRadioButton splittingOff;
    private JRadioButton splittingDelayed;
    private JRadioButton depOn;
    private JRadioButton depOff;
    private JRadioButton queryOn;
    private JRadioButton queryRestricted; 
    private JRadioButton queryOff;
    private JRadioButton queryAxiomOn;
    private JRadioButton queryAxiomOff;    
    private JRadioButton nonLinArithNone;
    private JRadioButton nonLinArithDefOps;
    private JRadioButton nonLinArithCompletion;
    private JRadioButton quantifierNone;
    private JRadioButton quantifierNonSplitting;
    private JRadioButton quantifierNonSplittingWithProgs;
    private JRadioButton quantifierInstantiate;
    private JRadioButton autoInductionOff; 
    private JRadioButton autoInductionRestricted; 
    private JRadioButton autoInductionLemmaOn; 
    
    private KeYMediator mediator;
    
//    private TimeoutSpinner timeoutSpinner;
    private JButton defaultButton;
    
    
    JPanel javaDLOptionsPanel = new JPanel() {
        
        /**
         * 
         */
        private static final long serialVersionUID = -6053300204350121172L;

        public void setEnabled(boolean enabled) {
             super.setEnabled(enabled);
             setChildrenEnabled(this, enabled);
        }

        private void setChildrenEnabled(Container container, boolean enabled) {
             for (int i=0; i<container.getComponentCount(); i++) {
                 Component comp = container.getComponent(i);
                 comp.setEnabled(enabled);
                 if (comp instanceof Container)
                     setChildrenEnabled((Container) comp, enabled);
             }
        }
    };
    
    JScrollPane javaDLOptionsScrollPane =
        new JScrollPane ( javaDLOptionsPanel,
                          ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED,
                          ScrollPaneConstants.HORIZONTAL_SCROLLBAR_NEVER );
    
    
    Border loweredetched = 
//        BorderFactory.createEtchedBorder(EtchedBorder.LOWERED);
        BorderFactory.createEmptyBorder();

    private final MainWindow mainWindow;

    
    public StrategySelectionView (MainWindow mainWindow) {        
        this.mainWindow = mainWindow;
        layoutPane();       
        refresh(mediator == null ? null : mediator.getSelectedProof());
	setVisible( true );
        addComponentListener(new java.awt.event.ComponentAdapter() {
            public void componentShown(java.awt.event.ComponentEvent e) {
                maxSlider.refresh();
//                timeoutSpinner.refresh();
            }
        });
    }
    
    private JRadioButton newButton(String text,
			String command, boolean selected, boolean enabled) {
    	JRadioButton result = new JRadioButton(text);
    	result.setEnabled(enabled);        
        result.setActionCommand(command);        
        buttonHashmap.put(command, result);        
		return result;
	}
    
    private JRadioButton getStrategyButton(String name) {
        return buttonHashmap.get(name);      
    }

	/** Build everything */    
    private void layoutPane() {        

        javaDLOptionsPanel.setEnabled(true);

        
        StratListener stratListener = new StratListener();
        OptListener optListener = new OptListener();
        
        this.setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));

        javaDLOptionsScrollPane
            .setBorder(BorderFactory.createTitledBorder("Java DL Options") );
        GridBagConstraints gbcpanel5 = new GridBagConstraints();
        final GridBagLayout javaDLOptionsLayout = new GridBagLayout ();
        javaDLOptionsPanel.setLayout(javaDLOptionsLayout);
                
        javaDLOptionsScrollPane.getVerticalScrollBar().setUnitIncrement(10);
        
//        javaDLOptionsPanel.setBorder(BorderFactory.createEmptyBorder());
        
        ////////////////////////////////////////////////////////////////////////

        int yCoord = 0;

        ////////////////////////////////////////////////////////////////////////
        ++yCoord;
        
        addJavaDLOption ( new JLabel ( "Stop at" ),
                    javaDLOptionsLayout, 1, yCoord, 7 );
        
        ++yCoord;

        rdBut17 = newButton("Default", StrategyProperties.STOPMODE_DEFAULT, true, false);
	rdBut17.setToolTipText(JavaCardDLStrategy.Factory.TOOL_TIP_STOP_AT_DEFAULT);
        stopModeGroup.add(rdBut17);
        addJavaDLOption ( rdBut17, javaDLOptionsLayout, 2, yCoord, 2 );        

        rdBut18 = newButton(
                "Unclosable", StrategyProperties.STOPMODE_NONCLOSE, false, false);
	rdBut18.setToolTipText(JavaCardDLStrategy.Factory.TOOL_TIP_STOP_AT_UNCLOSABLE);
        stopModeGroup.add(rdBut18);
        addJavaDLOption ( rdBut18, javaDLOptionsLayout, 4, yCoord, 2 );        
       
        
        ++yCoord;
        addJavaDLOptionSpace ( javaDLOptionsLayout, yCoord );
        ////////////////////////////////////////////////////////////////////////        
       
        ++yCoord;
        addJavaDLOptionSpace ( javaDLOptionsLayout, yCoord );
        ////////////////////////////////////////////////////////////////////////

        
        addJavaDLOption ( new JLabel ( "Proof splitting" ),
                    javaDLOptionsLayout, 1, yCoord, 7 );

        ++yCoord;
        
        splittingNormal = newButton("Free",
                       StrategyProperties.SPLITTING_NORMAL, false, false);
        splittingGroup.add(splittingNormal);
        addJavaDLOption ( splittingNormal, javaDLOptionsLayout, 2, yCoord, 2 );     
        splittingNormal.setToolTipText(JavaCardDLStrategy.Factory.TOOL_TIP_PROOF_SPLITTING_FREE);
        

        splittingDelayed = newButton("Delayed",
                     StrategyProperties.SPLITTING_DELAYED, true, false);
        splittingDelayed.setToolTipText(JavaCardDLStrategy.Factory.TOOL_TIP_PROOF_SPLITTING_DELAYED);
        splittingGroup.add(splittingDelayed);
        addJavaDLOption ( splittingDelayed, javaDLOptionsLayout, 4, yCoord, 2 );

        splittingOff = newButton("Off",
                     StrategyProperties.SPLITTING_OFF, false, false);
        splittingOff.setToolTipText(JavaCardDLStrategy.Factory.TOOL_TIP_PROOF_SPLITTING_OFF);
        splittingGroup.add(splittingOff);
        addJavaDLOption ( splittingOff, javaDLOptionsLayout, 6, yCoord, 2 );

        ++yCoord;
        addJavaDLOptionSpace ( javaDLOptionsLayout, yCoord );
        
        ////////////////////////////////////////////////////////////////////////

        ++yCoord;
        
        addJavaDLOption ( new JLabel ( "Loop treatment" ),
                    javaDLOptionsLayout, 1, yCoord, 7 );
        
        ++yCoord;

        rdBut10 = newButton("Invariant", StrategyProperties.LOOP_INVARIANT, false, false);
        rdBut10.setToolTipText(JavaCardDLStrategy.Factory.TOOL_TIP_LOOP_INVARIANT);
        loopGroup.add(rdBut10);
        addJavaDLOption ( rdBut10, javaDLOptionsLayout, 2, yCoord, 2 );

        rdBut9 = newButton("Expand", StrategyProperties.LOOP_EXPAND, true, false);
        rdBut9.setToolTipText(JavaCardDLStrategy.Factory.TOOL_TIP_LOOP_EXPAND);
        loopGroup.add(rdBut9);
        addJavaDLOption ( rdBut9, javaDLOptionsLayout, 4, yCoord, 2 );

        rdBut11 = newButton("None", StrategyProperties.LOOP_NONE, false, false);
        rdBut11.setToolTipText(JavaCardDLStrategy.Factory.TOOL_TIP_LOOP_NONE);
        loopGroup.add(rdBut11);
        addJavaDLOption ( rdBut11, javaDLOptionsLayout, 6, yCoord, 2 );        

        ++yCoord;
        addJavaDLOptionSpace ( javaDLOptionsLayout, yCoord );

        ////////////////////////////////////////////////////////////////////////

        ++yCoord;

        addJavaDLOption(new JLabel("Block treatment"), javaDLOptionsLayout, 1, yCoord, 7);

        ++yCoord;

        blockContractRadioButton = newButton("Contract", StrategyProperties.BLOCK_CONTRACT, false, false);
        blockContractRadioButton.setToolTipText(JavaCardDLStrategy.Factory.TOOL_TIP_BLOCK_CONTRACT);
        blockGroup.add(blockContractRadioButton);
        addJavaDLOption(blockContractRadioButton, javaDLOptionsLayout, 2, yCoord, 2);

        blockExpandRadioButton = newButton("Expand", StrategyProperties.BLOCK_EXPAND, true, false);
        blockExpandRadioButton.setToolTipText(JavaCardDLStrategy.Factory.TOOL_TIP_BLOCK_EXPAND);
        blockGroup.add(blockExpandRadioButton);
        addJavaDLOption(blockExpandRadioButton, javaDLOptionsLayout, 4, yCoord, 2);

        //TODO Implement Strategy 'None' for Block contracts. 'None' means, that the solver stops if it encounters an (applicable) block contract.
        /*blockNoneRadioButton = newButton("None", StrategyProperties.BLOCK_NONE, false, false);
        blockGroup.add(blockNoneRadioButton);
        addJavaDLOption(blockNoneRadioButton, javaDLOptionsLayout, 6, yCoord, 2);*/

        ++yCoord;
        addJavaDLOptionSpace (javaDLOptionsLayout, yCoord);

        ////////////////////////////////////////////////////////////////////////

        ++yCoord;
        
        addJavaDLOption ( new JLabel ( "Method treatment" ),
                    javaDLOptionsLayout, 1, yCoord, 7 );
        
        ++yCoord;

        rdBut13 = newButton(
                "Contract", StrategyProperties.METHOD_CONTRACT, false, false);
        rdBut13.setToolTipText(JavaCardDLStrategy.Factory.TOOL_TIP_METHOD_CONTRACT);
        methodGroup.add(rdBut13);
        addJavaDLOption ( rdBut13, javaDLOptionsLayout, 2, yCoord, 2 );        

        rdBut12 = newButton("Expand", StrategyProperties.METHOD_EXPAND, true, false);
        rdBut12.setToolTipText(JavaCardDLStrategy.Factory.TOOL_TIP_METHOD_EXPAND);
        methodGroup.add(rdBut12);
        addJavaDLOption ( rdBut12, javaDLOptionsLayout, 4, yCoord, 2 );        

        rdBut14 = newButton("None",
                StrategyProperties.METHOD_NONE, false, false);
        rdBut14.setToolTipText(JavaCardDLStrategy.Factory.TOOL_TIP_METHOD_NONE);
        methodGroup.add(rdBut14);
        addJavaDLOption ( rdBut14, javaDLOptionsLayout, 6, yCoord, 2 );        
        
        ++yCoord;
        addJavaDLOptionSpace ( javaDLOptionsLayout, yCoord );

        ////////////////////////////////////////////////////////////////////////

        ++yCoord;
        
        addJavaDLOption ( new JLabel ( "Dependency contracts" ),
                    javaDLOptionsLayout, 1, yCoord, 7 );
        
        ++yCoord;

        depOn = newButton("On", 
                StrategyProperties.DEP_ON, false, false);
        depOn.setToolTipText(JavaCardDLStrategy.Factory.TOOL_TIP_DEPENDENCY_ON);
        depGroup.add(depOn);
        addJavaDLOption ( depOn, javaDLOptionsLayout, 2, yCoord, 2 );        
        
        depOff = newButton("Off", 
                StrategyProperties.DEP_OFF, false, false);
        depOff.setToolTipText(JavaCardDLStrategy.Factory.TOOL_TIP_DEPENDENCY_OFF);
//        queryProgramsToRight.setToolTipText ( "<html>Move all program blocks to the" +
//                                              " succedent.<br>" +
//                                              " This is necessary" +
//                                              " when query invocations<br>" +
//                                              " are" +
//                                              " supposed to be eliminated" +
//                                              " using<br>" +
//                                              " method contracts.</html>" );
        depGroup.add(depOff);
        addJavaDLOption ( depOff, javaDLOptionsLayout, 4, yCoord, 2 );

        
        ++yCoord;
        addJavaDLOptionSpace ( javaDLOptionsLayout, yCoord );

        ////////////////////////////////////////////////////////////////////////

        ++yCoord;
        
        addJavaDLOption ( new JLabel ( "Query treatment" ),
                    javaDLOptionsLayout, 1, yCoord, 7 );
        
        ++yCoord;

        queryOn = newButton("On", 
                StrategyProperties.QUERY_ON, false, false);
        queryOn.setToolTipText(JavaCardDLStrategy.Factory.TOOL_TIP_QUERY_ON);
        queryGroup.add(queryOn);
        addJavaDLOption ( queryOn, javaDLOptionsLayout, 2, yCoord, 2 );        
        
        queryRestricted = newButton("Restricted", 
                StrategyProperties.QUERY_RESTRICTED, false, false);
        queryRestricted.setToolTipText (JavaCardDLStrategy.Factory.TOOL_TIP_QUERY_RESTRICTED); 
        queryGroup.add(queryRestricted);
        addJavaDLOption ( queryRestricted, javaDLOptionsLayout, 4, yCoord, 2 );        

        queryOff = newButton("Off", 
                StrategyProperties.QUERY_OFF, false, false);
        queryOff.setToolTipText(JavaCardDLStrategy.Factory.TOOL_TIP_QUERY_OFF);

        queryGroup.add(queryOff);
        addJavaDLOption ( queryOff, javaDLOptionsLayout, 6, yCoord, 2 );

        
        ++yCoord;
        
        queryAxiomOn = newButton("On", 
                StrategyProperties.QUERYAXIOM_ON, false, false);
        queryAxiomOn.setToolTipText(JavaCardDLStrategy.Factory.TOOL_TIP_EXPAND_LOCAL_QUERIES_ON);
        queryAxiomGroup.add(queryAxiomOn);

        queryAxiomOff = newButton("Off", 
                StrategyProperties.QUERYAXIOM_OFF, false, false);
        queryAxiomOff.setToolTipText(JavaCardDLStrategy.Factory.TOOL_TIP_EXPAND_LOCAL_QUERIES_OFF);
        queryAxiomGroup.add(queryAxiomOff);

        JPanel queryAxiomPanel = new JPanel();
        JLabel queryAxiomLabel = new JLabel("Expand local queries:");
        	queryAxiomLabel.setToolTipText(JavaCardDLStrategy.Factory.TOOL_TIP_EXPAND_LOCAL_QUERIES_ON);
        queryAxiomPanel.add(queryAxiomLabel);
        queryAxiomPanel.add(queryAxiomOn);
        queryAxiomPanel.add(queryAxiomOff);
        addJavaDLOption (queryAxiomPanel, javaDLOptionsLayout, 2, yCoord, 7 );        
        
        ++yCoord;
        addJavaDLOptionSpace ( javaDLOptionsLayout, yCoord );
       
        
  
        ++yCoord;
        
        addJavaDLOption ( new JLabel ( "Arithmetic treatment" ),
                    javaDLOptionsLayout, 1, yCoord, 7 );
        
        ++yCoord;

        nonLinArithNone = newButton("Basic", 
                StrategyProperties.NON_LIN_ARITH_NONE, true, false);
        nonLinArithNone.setToolTipText(JavaCardDLStrategy.Factory.TOOL_TIP_ARITHMETIC_BASE);
        nonLinArithGroup.add(nonLinArithNone);
        addJavaDLOption ( nonLinArithNone, javaDLOptionsLayout, 2, yCoord, 2 );
                                          
        nonLinArithDefOps = newButton("DefOps", 
                StrategyProperties.NON_LIN_ARITH_DEF_OPS, false, false);
        nonLinArithDefOps.setToolTipText (JavaCardDLStrategy.Factory.TOOL_TIP_ARITHMETIC_DEF_OPS);
        nonLinArithGroup.add(nonLinArithDefOps);
        addJavaDLOption ( nonLinArithDefOps, javaDLOptionsLayout, 4, yCoord, 2 );

        nonLinArithCompletion = newButton("Model Search", 
                StrategyProperties.NON_LIN_ARITH_COMPLETION, false, false);
        nonLinArithCompletion.setToolTipText (JavaCardDLStrategy.Factory.TOOL_TIP_ARITHMETIC_MODEL_SEARCH);
        nonLinArithGroup.add(nonLinArithCompletion);
        addJavaDLOption ( nonLinArithCompletion, javaDLOptionsLayout, 6, yCoord, 2 );
        
        ++yCoord;
        addJavaDLOptionSpace ( javaDLOptionsLayout, yCoord );

        ////////////////////////////////////////////////////////////////////////

        ++yCoord;
        
        addJavaDLOption ( new JLabel ( "Quantifier treatment" ),
                    javaDLOptionsLayout, 1, yCoord, 7 );
        
        ++yCoord;
        
        quantifierNone = newButton("None", 
                         StrategyProperties.QUANTIFIERS_NONE, true, false);
        quantifierNone.setToolTipText (JavaCardDLStrategy.Factory.TOOL_TIP_QUANTIFIER_NONE);
        quantifierGroup.add(quantifierNone);
        addJavaDLOption ( quantifierNone, javaDLOptionsLayout, 2, yCoord, 4 );

        quantifierNonSplitting = newButton("No Splits", 
                             StrategyProperties.QUANTIFIERS_NON_SPLITTING, true, false);
        quantifierNonSplitting.setToolTipText (JavaCardDLStrategy.Factory.TOOL_TIP_QUANTIFIER_NO_SPLITS);
        quantifierGroup.add(quantifierNonSplitting);
        addJavaDLOption ( quantifierNonSplitting, javaDLOptionsLayout, 6, yCoord, 2 );

        ++yCoord;

        quantifierNonSplittingWithProgs
                 = newButton("No Splits with Progs", 
            StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS, true, false);
        quantifierNonSplittingWithProgs.setToolTipText (JavaCardDLStrategy.Factory.TOOL_TIP_QUANTIFIER_NO_SPLITS_WITH_PROGS);
        quantifierGroup.add(quantifierNonSplittingWithProgs);
        addJavaDLOption ( quantifierNonSplittingWithProgs, javaDLOptionsLayout, 2, yCoord, 4 );

        quantifierInstantiate = newButton("Free", 
                              StrategyProperties.QUANTIFIERS_INSTANTIATE, true, false);
        quantifierInstantiate.setToolTipText (JavaCardDLStrategy.Factory.TOOL_TIP_QUANTIFIER_FREE);
        quantifierGroup.add(quantifierInstantiate);
        addJavaDLOption ( quantifierInstantiate, javaDLOptionsLayout, 6, yCoord, 2 );

        ++yCoord;
        addJavaDLOptionSpace ( javaDLOptionsLayout, yCoord );

        ////////////////////////////////////////////////////////////////////////
        //chrisg
        
        ++yCoord;
        
        addJavaDLOption ( new JLabel ( "Auto Induction" ),
                    javaDLOptionsLayout, 1, yCoord, 7 );
        
        ++yCoord;

        /*  autoInductionOn = newButton("On", 
        StrategyProperties.AUTO_INDUCTION_ON, false, false);
        autoInductionOn.setToolTipText ( "<html>" +
            "Create an inductive proof for formulas of the form:<br>" +
            "      ==>  \\forall int i; 0&lt;=i->phi <br>" +
            "and certain other forms. The induction hypothesis<br>" +
            "is the subformula phi. The rule is applied before<br>" +
            "beta rules are applied." +
            "</html>" );
            autoInductionGroup.add(autoInductionOn);
            addJavaDLOption ( autoInductionOn, javaDLOptionsLayout, 4, yCoord, 2 );
          */
        
        //The old "use as lemma" setting is now the "on" setting.
        autoInductionLemmaOn = newButton("On", 
                StrategyProperties.AUTO_INDUCTION_LEMMA_ON, false, false);
        
        autoInductionLemmaOn.setToolTipText (JavaCardDLStrategy.Factory.TOOL_TIP_AUTO_INDUCTION_ON);
            autoInductionGroup.add(autoInductionLemmaOn);
            addJavaDLOption ( autoInductionLemmaOn, javaDLOptionsLayout, 2, yCoord, 2 );
            
        
       autoInductionRestricted = newButton("Restricted", 
                    StrategyProperties.AUTO_INDUCTION_RESTRICTED, false, false);
       autoInductionRestricted.setToolTipText (JavaCardDLStrategy.Factory.TOOL_TIP_AUTO_INDUCTION_RESTRICTED);
       autoInductionGroup.add(autoInductionRestricted);
       addJavaDLOption ( autoInductionRestricted, javaDLOptionsLayout, 4, yCoord, 2 );

   
        autoInductionOff = newButton("Off", 
                         StrategyProperties.AUTO_INDUCTION_OFF, true, false);
        autoInductionOff.setToolTipText (JavaCardDLStrategy.Factory.TOOL_TIP_AUTO_INDUCTION_OFF);
        autoInductionGroup.add(autoInductionOff);
        addJavaDLOption ( autoInductionOff, javaDLOptionsLayout, 6, yCoord, 2 );

     

        
        ++yCoord;
        addJavaDLOptionSpace ( javaDLOptionsLayout, yCoord );

        ////////////////////////////////////////////////////////////////////////

        ++yCoord;

        final JLabel userTacletsLabel = new JLabel ( "User-specific taclet sets" );
        addJavaDLOption ( userTacletsLabel, javaDLOptionsLayout, 1, yCoord, 7 );
        userTacletsLabel.setToolTipText("<html>" +
                                        "These options define whether user- and problem-specific taclet sets<br>" +
                                        "are applied automatically by the strategy. Problem-specific taclets<br>" +
                                        "can be defined in the \\rules-section of a .key-problem file. For<br>" +
                                        "automatic application, the taclets have to contain a clause<br>" +
                                        "\\heuristics(userTaclets1), \\heuristics(userTaclets2), etc." +
                                        "</html>");
        
        for (int i = 1; i <= StrategyProperties.USER_TACLETS_NUM; ++i) {
            ++yCoord;
            addUserTacletsOptions ( javaDLOptionsLayout, optListener,
                                    userTacletsGroup[i-1], yCoord, i );
        }

        fixVerticalSpace ( javaDLOptionsScrollPane );

        ////////////////////////////////////////////////////////////////////////

        Box box = Box.createVerticalBox();

        
        JButton go = new JButton(mainWindow.getAutoModeAction());
        
        JPanel timeout = createTimeoutSpinner();

        JPanel goPanel = new JPanel ();
        GridBagLayout goLayout = new GridBagLayout();
        goPanel.setLayout(goLayout);
        goPanel.setAlignmentX(Component.LEFT_ALIGNMENT);
        
        gbcpanel5.gridx = 1;
        gbcpanel5.gridy = 0;
        gbcpanel5.gridwidth = 1;
        gbcpanel5.gridheight = 1;
        gbcpanel5.fill = GridBagConstraints.NONE;
        gbcpanel5.weightx = 1;
        gbcpanel5.weighty = 0;
        gbcpanel5.anchor = GridBagConstraints.WEST;
        gbcpanel5.insets = new Insets (4, 4, 4, 4);
        goLayout.setConstraints(go, gbcpanel5);
        goPanel.add(go);
        
        gbcpanel5.gridx = 2;
        gbcpanel5.gridy = 0;
        gbcpanel5.gridwidth = 1;
        gbcpanel5.gridheight = 1;
        gbcpanel5.fill = GridBagConstraints.NONE;
        gbcpanel5.weightx = 1;
        gbcpanel5.weighty = 0;
        gbcpanel5.anchor = GridBagConstraints.WEST;
        gbcpanel5.insets = new Insets (0, 0, 0, 0);        
        
        gbcpanel5.gridx = 3;
        gbcpanel5.gridy = 0;
        gbcpanel5.gridwidth = 1;
        gbcpanel5.gridheight = 1;
        gbcpanel5.fill = GridBagConstraints.NONE;
        gbcpanel5.weightx = 0;
        gbcpanel5.weighty = 0;
        gbcpanel5.anchor = GridBagConstraints.CENTER;
        gbcpanel5.insets = new Insets (0, 0, 0, 0);
        goLayout.setConstraints(timeout, gbcpanel5);
        goPanel.add(timeout);
        
        fixVerticalSpace ( goPanel );

        

        box.add(Box.createVerticalStrut(4));
        box.add(goPanel);       
        box.add(Box.createVerticalStrut(8));
//        box.add(numLabel);
//        box.add(Box.createVerticalStrut(4));
        maxSlider.setAlignmentX(Component.LEFT_ALIGNMENT);
        box.add(maxSlider);
        box.add(Box.createVerticalStrut(8));

        javaDLOptionsScrollPane.setAlignmentX(Component.LEFT_ALIGNMENT);
        box.add(javaDLOptionsScrollPane);       
	
       
        // HACK but I really do not know enough about the GridBagLayout :-(
//        final JPanel verticalGlue = new JPanel();
//        verticalGlue.setPreferredSize(new Dimension(1, 1024));
//        box.add(verticalGlue);
        box.add(Box.createVerticalGlue());

        this.add(box);
        //  add the ActionListener to the Buttons and ActionCommands 
        //  for identifying Buttons
       // bSimpleJavaCardDLStrategy.addActionListener(stratListener);
        rdBut9.addActionListener(optListener);	
        rdBut10.addActionListener(optListener);
        rdBut11.addActionListener(optListener);
        rdBut12.addActionListener(optListener);       
        rdBut13.addActionListener(optListener);     
        rdBut14.addActionListener(optListener);
        rdBut17.addActionListener(optListener);
        rdBut18.addActionListener(optListener);
        blockContractRadioButton.addActionListener(optListener);
        blockExpandRadioButton.addActionListener(optListener);
        //blockNoneRadioButton.addActionListener(optListener);
        depOn.addActionListener(optListener);
        depOff.addActionListener(optListener);
        queryOn.addActionListener(optListener);
        queryRestricted.addActionListener(optListener);
        queryOff.addActionListener(optListener);
        queryAxiomOn.addActionListener(optListener);
        queryAxiomOff.addActionListener(optListener);
        splittingNormal.addActionListener(optListener);
        splittingDelayed.addActionListener(optListener);
        splittingOff.addActionListener(optListener);
        nonLinArithNone.addActionListener(optListener);
        nonLinArithDefOps.addActionListener(optListener);
        nonLinArithCompletion.addActionListener(optListener);
        quantifierNone.addActionListener(optListener);
        quantifierNonSplitting.addActionListener(optListener);
        quantifierNonSplittingWithProgs.addActionListener(optListener);
        quantifierInstantiate.addActionListener(optListener);
        autoInductionOff.addActionListener(optListener);
        autoInductionRestricted.addActionListener(optListener);
        autoInductionLemmaOn.addActionListener(optListener);
    }

    private void addUserTacletsOptions(GridBagLayout javaDLOptionsLayout,
                                       OptListener optListener,
                                       ButtonGroup group,
                                       int yCoord, int num) {
        addJavaDLOption ( new JLabel ( "" + num + ":  " ),
                          javaDLOptionsLayout, 2, yCoord, 1 );
        
        final JRadioButton userTacletsOff = newButton("Off", 
                        StrategyProperties.USER_TACLETS_OFF + num, true, false);
        userTacletsOff.setToolTipText(JavaCardDLStrategy.Factory.TOOL_TIP_USER_OFF(num));
        group.add(userTacletsOff);
        userTacletsOff.addActionListener(optListener);
        addJavaDLOption ( userTacletsOff, javaDLOptionsLayout, 3, yCoord, 1 );
        
        final JRadioButton userTacletsLow = newButton("Low prior.", 
                        StrategyProperties.USER_TACLETS_LOW + num, true, false);
        userTacletsLow.setToolTipText(JavaCardDLStrategy.Factory.TOOL_TIP_USER_LOW(num));
        group.add(userTacletsLow);
        userTacletsLow.addActionListener(optListener);
        addJavaDLOption ( userTacletsLow, javaDLOptionsLayout, 4, yCoord, 2 );
        
        final JRadioButton userTacletsHigh = newButton("High prior.", 
                         StrategyProperties.USER_TACLETS_HIGH + num, true, false);
        userTacletsHigh.setToolTipText(JavaCardDLStrategy.Factory.TOOL_TIP_USER_HIGH(num));
        group.add(userTacletsHigh);
        userTacletsHigh.addActionListener(optListener);
        addJavaDLOption ( userTacletsHigh, javaDLOptionsLayout, 6, yCoord, 2 );
    }

    private void addJavaDLOptionSpace(GridBagLayout javaDLOptionsLayout, int yCoord) {
        final GridBagConstraints con = new GridBagConstraints ();
        con.gridx = 0;
        con.gridy = yCoord;
        con.gridwidth = 9;
        con.gridheight = 1;
        con.fill = GridBagConstraints.HORIZONTAL;
        con.weightx = 1;
        con.weighty = 0;
        con.anchor = GridBagConstraints.CENTER;
        final Component sep = new JLabel ();
        javaDLOptionsLayout.setConstraints ( sep, con );
        javaDLOptionsPanel.add ( sep );
        addJavaDLOption ( Box.createRigidArea ( new Dimension ( 4, 4 ) ),
                          javaDLOptionsLayout, 0, yCoord, 1 );
        addJavaDLOption ( Box.createRigidArea ( new Dimension ( 4, 4 ) ),
                          javaDLOptionsLayout, 1, yCoord, 1 );
    }

    private void addJavaDLOption(Component widget,
                                 GridBagLayout javaDLOptionsLayout, int gridx,
                                 int gridy, int width) {
        final GridBagConstraints con = new GridBagConstraints ();
        con.gridx = gridx;
        con.gridy = gridy;
        con.gridwidth = width;
        con.gridheight = 1;
        con.fill = GridBagConstraints.NONE;
        con.weightx = 0;
        con.weighty = 0;
        con.anchor = GridBagConstraints.WEST;
        javaDLOptionsLayout.setConstraints ( widget, con );
        javaDLOptionsPanel.add ( widget );
    }

    private void fixVerticalSpace(JComponent comp) {
        comp.setMaximumSize
        ( new Dimension ( Integer.MAX_VALUE,
                          comp.getPreferredSize ().height ) );
    }
    
    private JPanel createTimeoutSpinner() {
//        final JPanel timeoutPanel = new JPanel();
//        timeoutPanel.setLayout(new FlowLayout());
//        final JLabel timeoutLabel = new JLabel("Time limit (ms)"); 
//        timeoutPanel.add(timeoutLabel);
//        timeoutPanel.setToolTipText("Interrupt automatic rule application " +
//                        "after the specified period of time (-1 disables timeout).");
//        
//        timeoutSpinner = new TimeoutSpinner();       
//        
//        timeoutSpinner.addChangeListener(new ChangeListener() {
//
//            public void stateChanged(ChangeEvent e) {
//                if (e.getSource() == timeoutSpinner) {
//                    long timeout = ((Long)((JSpinner)e.getSource()).getValue()).longValue();
//                    mediator.setAutomaticApplicationTimeout(timeout);
//                }
//            }            
//        });
//        timeoutPanel.add(timeoutSpinner);
//        return timeoutPanel;
	final JPanel panel = new JPanel();
	defaultButton = new JButton("Defaults");
	defaultButton.addActionListener(new ActionListener() {
	    public void actionPerformed(ActionEvent e) {
		mediator.getSelectedProof()
		        .getSettings()
		        .getStrategySettings()
		        .setMaxSteps(10000);
		updateStrategySettings(JAVACARDDL_STRATEGY_NAME,
			               new StrategyProperties());
		refresh(mediator.getSelectedProof());
	    }
	});
	panel.add(defaultButton);
	
        maxSlider.addChangeListener( new ChangeListener() {
            public void stateChanged ( ChangeEvent e ) {
        	refreshDefaultButton(); 
            }
        });
	
	return panel;
    }
    
    public void setMediator(KeYMediator mediator) {
        this.mediator = mediator;
        maxSlider.setMediator(mediator);
        
        mediator.addKeYSelectionListener(new SelectionChangedListener());
                
        final StrategyFactory defaultStrategyFactory = 
            mediator.getProfile().getDefaultStrategyFactory();
        

    }


    private final MaxRuleAppSlider maxSlider = new MaxRuleAppSlider(null);
    
    


//    class TimeoutSpinner extends JSpinner {        
//        public TimeoutSpinner() {
//            super(new SpinnerNumberModel
//                    (Long.valueOf(-1), Long.valueOf(-1), Long.valueOf(Long.MAX_VALUE), Long.valueOf(1))); 
//            if (this.getEditor() instanceof JSpinner.DefaultEditor) {
//                JFormattedTextField ftf = ((JSpinner.DefaultEditor)this.getEditor()).getTextField();
//                if (ftf != null) {
//                    ftf.setColumns(6); 
//                    ftf.setHorizontalAlignment(SwingConstants.RIGHT);
//                }
//            }            
//        }
//        
//        public void refresh() {
//            setValue(Long.valueOf(mediator.getAutomaticApplicationTimeout()));
//        }    
//    }

    /**
     * TODO: here should be a settings listener listening to strategy setting changes
     * Therefore we have to wait until ProofSettings have been refactored (see KeY-Wiki) 
     * 
     *(Currently changes made in the old slider are not reported to this view)
     */
    private final class SelectionChangedListener 
        implements KeYSelectionListener {
        
        public void selectedNodeChanged(KeYSelectionEvent e) {}

        public void selectedProofChanged(KeYSelectionEvent e) {
            refresh(e.getSource().getSelectedProof());            
        }        
    }

    
    /** performs a refresh of all elements in this tab */
    public void refresh(Proof proof) {
        if (proof == null) {            
            enableAll(false);                
        } else {
//            boolean methodExpandAllowed = false;
//            for(de.uka.ilkd.key.logic.Choice c 
//        	     : proof.env().getInitConfig().getActivatedChoices()) {
//        	if(c.name().toString().equals("methodExpand:allow")) {
//        	    methodExpandAllowed = true;
//        	    break;
//        	}
//            }
//            rdBut12.setEnabled(methodExpandAllowed);                        
//            if(!methodExpandAllowed && rdBut12.isSelected()) {
//        	rdBut13.doClick();
//            }
            
            String activeS = proof.getActiveStrategy().name().toString();
            JRadioButton bactive = getStrategyButton(activeS);
            if (bactive != null) { // That bactive is null is a valid scenario for instance in the symbolic execution debugger
               bactive.setSelected(true);
            }
            
            StrategyProperties p = proof.
                getSettings().getStrategySettings().
                    getActiveStrategyProperties();
            String activeSplittingOptions = p.getProperty(StrategyProperties.SPLITTING_OPTIONS_KEY);
            JRadioButton bSplittingActive = getStrategyOptionButton(activeSplittingOptions,
		    StrategyProperties.SPLITTING_OPTIONS_KEY);
            bSplittingActive.setSelected(true);
            String activeLoopOptions = p.getProperty(StrategyProperties.LOOP_OPTIONS_KEY);
            JRadioButton bLoopActive = getStrategyOptionButton(activeLoopOptions, 
                    StrategyProperties.LOOP_OPTIONS_KEY);
            bLoopActive.setSelected(true);
            String activeBlockOptions = p.getProperty(StrategyProperties.BLOCK_OPTIONS_KEY);
            JRadioButton bBlockActive = getStrategyOptionButton(activeBlockOptions, 
                    StrategyProperties.BLOCK_OPTIONS_KEY);
            bBlockActive.setSelected(true);
            String activeMethodOptions = p.getProperty(StrategyProperties.METHOD_OPTIONS_KEY);
            JRadioButton bMethodActive = getStrategyOptionButton(activeMethodOptions, 
                    StrategyProperties.METHOD_OPTIONS_KEY);
            bMethodActive.setSelected(true);   
            String activeDepOptions = p.getProperty(StrategyProperties.DEP_OPTIONS_KEY);
            JRadioButton bDepActive = getStrategyOptionButton(activeDepOptions, 
                    StrategyProperties.DEP_OPTIONS_KEY);
            bDepActive.setSelected(true);   
            String activeQueryOptions = p.getProperty(StrategyProperties.QUERY_OPTIONS_KEY);
            JRadioButton bQueryActive = getStrategyOptionButton(activeQueryOptions, 
                    StrategyProperties.QUERY_OPTIONS_KEY);
            bQueryActive.setSelected(true);   
            String activeQueryAxOptions = p.getProperty(StrategyProperties.QUERYAXIOM_OPTIONS_KEY);
            JRadioButton bQueryAxActive = getStrategyOptionButton(activeQueryAxOptions, 
                    StrategyProperties.QUERYAXIOM_OPTIONS_KEY);
            bQueryAxActive.setSelected(true);   
            String activeNonLinArithOptions = p.getProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY);
            JRadioButton bNonLinArithActive = getStrategyOptionButton(activeNonLinArithOptions, 
                    StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY);
            bNonLinArithActive.setSelected(true);   
            String quantifierOptions = p.getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY);
            JRadioButton bQuantifierActive = getStrategyOptionButton(quantifierOptions, 
                    StrategyProperties.QUANTIFIERS_OPTIONS_KEY);
            bQuantifierActive.setSelected(true);   
            String stopmodeOptions = p.getProperty(StrategyProperties.STOPMODE_OPTIONS_KEY);
            JRadioButton bStopModeActive = getStrategyOptionButton(stopmodeOptions, 
                    StrategyProperties.STOPMODE_OPTIONS_KEY);
            bStopModeActive.setSelected(true);            
            String autoInductionOptions = p.getProperty(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY); 
            JRadioButton bAutoInductionOptions = getStrategyOptionButton(autoInductionOptions, 
                    StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY);
            bAutoInductionOptions.setSelected(true);   
         
            for (int i = 1; i <= StrategyProperties.USER_TACLETS_NUM; ++i) {
                String userTacletsOptions =
                    p.getProperty(StrategyProperties.USER_TACLETS_OPTIONS_KEY(i));
                JRadioButton userTacletsActive = getStrategyOptionButton(userTacletsOptions + i,
                    StrategyProperties.USER_TACLETS_OFF);
                userTacletsActive.setSelected(true);
            }
            
            maxSlider.refresh();
//            timeoutSpinner.refresh();
            javaDLOptionsPanel.setEnabled(true);
            enableAll(true);
            
            refreshDefaultButton();
        }
    }
    
    
    private void refreshDefaultButton() {
	defaultButton.setEnabled(mediator.getSelectedProof() != null
				 && (maxSlider.getPos() != 10000
		                    || !getProperties().isDefault()));	
    }
    

    private JRadioButton getStrategyOptionButton(String activeOptions, String category) {
        JRadioButton bActive = getStrategyButton(activeOptions);
        if (bActive == null) {
            System.err.println("Unknown option '" + activeOptions + "' falling back to " + 
                    StrategyProperties.getDefaultProperty(category));
            bActive = getStrategyButton(StrategyProperties.getDefaultProperty(category));
        }
        return bActive;
    }


    
    /**
     * enables or disables all components
     * @param enable boolean saying whether to activate or
     * deactivate the components
     */
    private void enableAll(boolean enable) {             
        maxSlider.setEnabled(enable);     
//        timeoutSpinner.setEnabled(enable);
        defaultButton.setEnabled(enable);
    	javaDLOptionsPanel.setEnabled(enable);

    }

    public Strategy getStrategy(String strategyName, 
	    			Proof proof,
	    			StrategyProperties properties) {
        if (mediator != null) {        
            final Iterator<StrategyFactory> supportedStrategies = 
               mediator.getProfile().supportedStrategies().iterator();
            while (supportedStrategies.hasNext()) {                
                final StrategyFactory s = supportedStrategies.next();
                if (strategyName.equals(s.name().toString())) {                    
                    return s.create(proof, properties);
                }
            }
            System.err.println("Selected Strategy '" + strategyName + "' not found falling back to "+ 
                mediator.getProfile().getDefaultStrategyFactory().name());
        }
        return mediator != null ? mediator.getProfile().getDefaultStrategyFactory().create(proof, properties) :
        	proof.getServices().getProfile().getDefaultStrategyFactory().create(proof, properties);
    }
  
    private String removeLast(String str, int num) {
        return str.substring ( 0, str.length () - num );
    }
    
    
    /**
     * @return the StrategyProperties
     */
    private StrategyProperties getProperties() {
        StrategyProperties p = new StrategyProperties();        
        p.setProperty( StrategyProperties.SPLITTING_OPTIONS_KEY, 
                       splittingGroup.getSelection().getActionCommand());
        p.setProperty( StrategyProperties.LOOP_OPTIONS_KEY, 
                       loopGroup.getSelection().getActionCommand());
        p.setProperty( StrategyProperties.BLOCK_OPTIONS_KEY, 
                	   blockGroup.getSelection().getActionCommand());
        p.setProperty( StrategyProperties.METHOD_OPTIONS_KEY, 
                       methodGroup.getSelection().getActionCommand());
        p.setProperty( StrategyProperties.DEP_OPTIONS_KEY, 
                       depGroup.getSelection().getActionCommand());
        p.setProperty( StrategyProperties.QUERY_OPTIONS_KEY, 
                       queryGroup.getSelection().getActionCommand());
        p.setProperty( StrategyProperties.QUERYAXIOM_OPTIONS_KEY, 
                       queryAxiomGroup.getSelection().getActionCommand());
        p.setProperty( StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, 
                       nonLinArithGroup.getSelection().getActionCommand());
        p.setProperty( StrategyProperties.QUANTIFIERS_OPTIONS_KEY, 
                       quantifierGroup.getSelection().getActionCommand());
        p.setProperty( StrategyProperties.STOPMODE_OPTIONS_KEY, 
                       stopModeGroup.getSelection().getActionCommand());
        p.setProperty( StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY, 
                       autoInductionGroup.getSelection().getActionCommand());
        
        for (int i = 1; i <= StrategyProperties.USER_TACLETS_NUM; ++i) {
            p.setProperty( StrategyProperties.USER_TACLETS_OPTIONS_KEY(i), 
                           removeLast(userTacletsGroup[i-1].getSelection()
                                      .getActionCommand(), 1));
        }
        
        return p;
    }

    
    private void updateStrategySettings(String strategyName,
	    				StrategyProperties p) {
        final Proof proof = mediator.getSelectedProof();
        final Strategy strategy = getStrategy(strategyName, proof, p);

        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().
        setStrategy(strategy.name());
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().
            setActiveStrategyProperties(p);
        
        proof.getSettings().getStrategySettings().
        setStrategy(strategy.name());
        proof.getSettings().getStrategySettings().
            setActiveStrategyProperties(p);
        
        proof.setActiveStrategy(strategy);
        
        refresh(proof);
    }

    public class StratListener implements ActionListener { 
        public void actionPerformed(ActionEvent e) {
            StrategyProperties props = getProperties();
            updateStrategySettings(e.getActionCommand(), props);
        }
    }

    public class OptListener implements ActionListener { 
        public void actionPerformed(ActionEvent e) { 	
            StrategyProperties props = getProperties();        	
            updateStrategySettings(
        	    mediator.getSelectedProof().getActiveStrategy().name().toString(),
                    props);
        }
    }
    

    private static class JRadioButtonHashMap extends JRadioButton {
        
        private static final long serialVersionUID = 7686260531440322733L;

        JRadioButtonHashMap(String text, String command, boolean selected, 
                boolean enabled) {
            super(text, selected);
            this.setEnabled(enabled);        
            this.setActionCommand(command);        
            hashmap.put(command, this);        
        }

        static HashMap<String, JRadioButtonHashMap> hashmap = new LinkedHashMap<String, JRadioButtonHashMap>();

        public static JRadioButton getButton(String command) {
            return hashmap.get(command);       
        }
    }

}
