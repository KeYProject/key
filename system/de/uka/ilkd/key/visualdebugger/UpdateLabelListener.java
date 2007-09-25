package de.uka.ilkd.key.visualdebugger;

import de.uka.ilkd.key.gui.RuleAppListener;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.proofevent.*;
import de.uka.ilkd.key.rule.*;

public class UpdateLabelListener implements RuleAppListener {


    public UpdateLabelListener() {
    }

    public void ruleApplied(ProofEvent e) {
        RuleAppInfo info = e.getRuleAppInfo();
        setStepInfos(info);        
        if (info != null) {
            Node parent = info.getOriginalNode();
            IteratorOfNodeReplacement it =info.getReplacementNodes();
            while(it.hasNext()){
                NodeReplacement nr = it.next();
                updateLabels(parent, nr,false);
                printLabels(nr.getNode());       
            }                       
        }               
    }


    private void setStepInfos(RuleAppInfo info) {
        final Node originalNode = info.getOriginalNode();
        SourceElement actSt = //this.getActStatement(originalNode);
            VisualDebugger.getVisualDebugger().determineFirstAndActiveStatement(originalNode);
        final VisualDebuggerState originalNodeVDS = originalNode.getNodeInfo().getVisualDebuggerState();

        int newCount = originalNodeVDS.getStatementIdcount();
        if (VisualDebugger.getVisualDebugger().isSepStatement((ProgramElement)(actSt))){            
            newCount--;
        }


        final IteratorOfNodeReplacement repl = info.getReplacementNodes();
        while(repl.hasNext()){
            NodeReplacement nr = repl.next();
            final VisualDebuggerState visualDebuggerState = nr.getNode().getNodeInfo().getVisualDebuggerState();
            visualDebuggerState.setStatementIdcount(newCount);
            visualDebuggerState.setStepOver(originalNodeVDS.getStepOver());
            visualDebuggerState.setStepOverFrom(originalNodeVDS.getStepOverFrom());
        }
    }

    //TODO in program mod!
    private boolean modalityTopLevel(PosInOccurrence pio){
        Term f = pio.constrainedFormula().formula(); 
        if (f.arity()>0){
            Term sub = f.sub(f.arity()-1);        
            if (sub.op() instanceof 
                    Modality)
                return true;
        }
        return false;
    }


    private boolean containsIfTerm(Term t){
        final OpCollector col = new OpCollector();
        t.execPreOrder(col);
        return col.contains(Op.IF_THEN_ELSE);        
    }

    private void updateLabels(Node parent, NodeReplacement nr, boolean impl){
        Node n = nr.getNode();
        int id=-1;
        boolean looking=false;

        HashMapFromPosInOccurrenceToLabel labels= (HashMapFromPosInOccurrenceToLabel)parent.getNodeInfo().getVisualDebuggerState().getLabels().clone();        

        RuleApp app = parent.getAppliedRuleApp();   

        if (app instanceof PosTacletApp){

            final PosTacletApp tapp = (PosTacletApp) app;
            final PosInOccurrence pio =  tapp.posInOccurrence().topLevel();


            if ((labels.containsKey(pio)&& isBCTaclet(tapp,parent))) {
                labels = setAssumeLabel(labels,n, tapp.ifFormulaInstantiations());


                if (modalityTopLevel(pio)&&!inUpdate(pio)){ 
                    id = nr.getNode().serialNr();
                    looking = true;

                }else {
                    id=((PCLabel)labels.get(pio)).getId();
                    looking = ((PCLabel)labels.get(pio)).isLooking();
                }

                IteratorOfNodeChange it =nr.getNodeChanges();               
                while (it.hasNext()){
                    NodeChange nc = it.next();
                    if (nc instanceof NodeChangeAddFormula){
                        labels.put(((NodeChangeAddFormula) nc).getPos(),
                                new PCLabel(id,looking));                        
                    } else if (nc instanceof NodeRedundantAddChange){
                        labels.put(((NodeRedundantAddChange)nc).getPio(), 
                                new PCLabel(id,looking));                        
                    } else if (nc instanceof NodeChangeRemoveFormula){
                        labels.remove(((NodeChangeRemoveFormula) nc).getPos());
                    }

                }

            }


        }else{
            // build in rule
            if (app.posInOccurrence()!=null){
                PosInOccurrence pio =  app.posInOccurrence().topLevel();
                if (labels.containsKey(pio)){
                    id=((PCLabel)labels.get(pio)).getId();
                    boolean isl = ((PCLabel)labels.get(pio)).isLooking();
                    IteratorOfNodeChange it =nr.getNodeChanges();               
                    while (it.hasNext()){
                        NodeChange nc = it.next();
                        if (nc instanceof NodeChangeAddFormula){        
                            labels.put(((NodeChangeAddFormula) nc).getPos(),new PCLabel(id,isl));
                        } else if (nc instanceof NodeChangeRemoveFormula){
                            labels.remove(((NodeChangeRemoveFormula) nc).getPos());
                        }   
                    }
                }

            }


        }
        updateLooking(labels);
        n.getNodeInfo().getVisualDebuggerState().setLabels(labels);
    }



    //TODO duplicatin in prooflistner
    private boolean isLiteral(PosInOccurrence pio){
        Term f=pio.constrainedFormula().formula();
        Operator op  = f.op();
        if(this.modalityTopLevel(pio) && !this.containsIfTerm(pio.constrainedFormula().formula()))
            return true;
        if (op== Op.AND || op== Op.OR ||op== Op.IF_THEN_ELSE||
                op== Op.IF_EX_THEN_ELSE ||
                op== Op.EQV || op== Op.IMP ||
                op== Op.AND || (op instanceof IUpdateOperator/* && !containsJavaBlock(pio.constrainedFormula().formula()*/))
            return false;  
        final OpCollector col = new OpCollector();
        f.execPostOrder(col);
        return !(col.contains(Op.IF_EX_THEN_ELSE)|| col.contains(Op.IF_THEN_ELSE));
    }


    private void updateLooking(HashMapFromPosInOccurrenceToLabel labels) {  
        boolean removelooking=true;

        for(IteratorOfPosInOccurrence it = labels.keyIterator();it.hasNext();){
            PosInOccurrence pio = it.next();
            PCLabel l = (PCLabel) labels.get(pio);
            if (l.isLooking()){
                if (!isLiteral(pio)){
                    removelooking=false;
                }
            }
        }

        if (removelooking){
            for(IteratorOfPosInOccurrence it = labels.keyIterator();it.hasNext();){
                PosInOccurrence pio = it.next();
                PCLabel l = (PCLabel) labels.get(pio);
                l.setLooking(false);
            }                                  
        }
    }


    private HashMapFromPosInOccurrenceToLabel setAssumeLabel(HashMapFromPosInOccurrenceToLabel labels,Node n, ListOfIfFormulaInstantiation inst){
        HashMapFromPosInOccurrenceToLabel l = labels;
        if (inst==null){
            return l;
        }
        IteratorOfIfFormulaInstantiation it = inst.iterator();
        while(it.hasNext()){
            //TODO case assume=find
            IfFormulaInstantiation next = it.next();
            if (next instanceof IfFormulaInstSeq){
                IfFormulaInstSeq i= (IfFormulaInstSeq) next;
                PosInOccurrence pio = new PosInOccurrence(i.getConstrainedFormula(),PosInTerm.TOP_LEVEL,i.inAntec());

                l.put(pio, new PCLabel(-1,false));

            }
        }
        return l;
    }

    private boolean isBCTaclet(PosTacletApp tap,Node n){
        return !(tap.taclet().name().toString().startsWith("inst_"));
    }

    private void printLabels(Node n){
        HashMapFromPosInOccurrenceToLabel map = n.getNodeInfo().getVisualDebuggerState().getLabels();

        String result = "Labels for node "+n.serialNr()+": ";
        if (map.size()==0)
            return ;  
        IteratorOfPosInOccurrence it=map.keyIterator();
        while(it.hasNext()){
            PosInOccurrence pio = it.next();
            Semisequent semi = pio.isInAntec() ? n.sequent().antecedent() : n.sequent().succedent();
            result = result +map.get(pio)+" "+(pio.isInAntec()?"A":("S"))+" "+semi.indexOf(pio.constrainedFormula())+" / ";
        }   
        VisualDebugger.print(result);
    }

    private void printLabels(HashMapFromPosInOccurrenceToLabel map,Sequent s ){

        if (map.size()==0)
            return ;
        String result = "Labels ";

        IteratorOfPosInOccurrence it=map.keyIterator();
        while(it.hasNext()){
            PosInOccurrence pio = it.next();
            Semisequent semi = pio.isInAntec() ? s.antecedent() : s.succedent();
            result = result +map.get(pio)+" "+(pio.isInAntec()?"A":("S"))+" "+semi.indexOf(pio.constrainedFormula())+" / ";
        }   
        VisualDebugger.print(result);
    }

    private boolean inUpdate(PosInOccurrence pio2){
        PosInOccurrence pio = pio2;
        while (!pio.isTopLevel()){
            pio = pio.up();
            if (pio.subTerm().op() instanceof QuanUpdateOperator){
                return true;                
            }
        }
        return false;
    }    
}
