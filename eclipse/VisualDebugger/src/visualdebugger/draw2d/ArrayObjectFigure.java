package visualdebugger.draw2d;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;

import org.eclipse.draw2d.*;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.swt.widgets.Display;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;
import de.uka.ilkd.key.visualdebugger.statevisualisation.SymbolicArrayObject;
import de.uka.ilkd.key.visualdebugger.statevisualisation.SymbolicObject;
import de.uka.ilkd.key.visualdebugger.statevisualisation.SymbolicObjectDiagram;

public class ArrayObjectFigure extends ObjectFigure {

    private final IndexLabel[] indexColumns;


    private Label[] indexConstrColumns;

    private LinkedList sos;

    public ArrayObjectFigure(SymbolicArrayObject sao, MouseListener listener,
            SymbolicObjectDiagram symbState,boolean pre) {
        super(sao, listener, symbState,pre);        
        this.sos = symbState.getSymbolicObjects();
        createConstr(listener);
        SetOfTerm indexes = sao.getAllIndexTerms();
        indexes=indexes.union(sao.getAllPostIndex());

        indexColumns = new IndexLabel[ indexes.size()];
        final IFigure compColumns = new Figure();
        int i =0;
        for(IteratorOfTerm it=indexes.iterator();it.hasNext();){
            final Term pv = it.next();
            indexColumns[ i ] = new IndexLabel(sao,pv,sos);
            indexColumns[ i ].addMouseListener(listener);
            i++;
        }
        sort(indexColumns);
        for(i=0;i<indexColumns.length;i++){
            compColumns.add( indexColumns[ i ] );
        }

        ToolbarLayout tbl = new ToolbarLayout( false );
        tbl.setMinorAlignment(ToolbarLayout.ALIGN_CENTER);
        tbl.setSpacing(5);
        compColumns.setLayoutManager(tbl );
        compColumns.setBorder( new SeparatorBorder() );
        add(compColumns);        

    }


    private SetOfTerm disj(SetOfTerm s1, SetOfTerm s2){
        SetOfTerm result = SetAsListOfTerm.EMPTY_SET;
        for(IteratorOfTerm it=s1.iterator();it.hasNext();){
            Term t = it.next();
            if(s2.contains(t))
                result=result.add(t);
        }
        return result;

    }


    private SetOfTerm exclude(SetOfTerm s1, SetOfTerm s2){
        SetOfTerm result = s1;
        for(IteratorOfTerm it=s2.iterator();it.hasNext();){
            Term t = it.next();
            if(s1.contains(t))
                result=result.remove(t);
        }
        return result;

    }



    private void createConstr(MouseListener listener) {
        LinkedList indexTermPos = 
            ((SymbolicArrayObject)this.getSymbolicObject()).
            getPossibleIndexTermConfigurations();
        if (indexTermPos.size()<=1)
            return;
        SetOfTerm cut= SetAsListOfTerm.EMPTY_SET;
        if (indexTermPos.size()>0){
            Iterator it = indexTermPos.iterator();
            cut = (SetOfTerm)it.next();
            while(it.hasNext()){
                cut = disj(cut, (SetOfTerm)it.next());
            }
        }



        //  System.out.println("Indizes "+attributes);
        indexConstrColumns = new Label[ indexTermPos.size()];
        final IFigure compColumns = new Figure();
        int i =0;
        for(Iterator it=indexTermPos.iterator();it.hasNext();){

            final SetOfTerm indexConstr = (SetOfTerm)it.next();
            // System.out.println("Term asfasfdagsfdasgfdsdf "+pv);
            indexConstrColumns[ i ] = new IndexConstraintLabel((SymbolicArrayObject)so,indexConstr,exclude(indexConstr, cut),sos);
            indexConstrColumns[ i ].setTextAlignment(PositionConstants.CENTER);
            indexConstrColumns[ i ].setFont( Display.getCurrent().getSystemFont() );
            indexConstrColumns[ i ].addMouseListener(listener);


            if (indexConstr.subset(
                    ((SymbolicArrayObject)this.getSymbolicObject()).getIndexConfiguration())){
                indexConstrColumns[i].setForegroundColor(ColorConstants.blue);
            }

            //   indexConstrColumns[ i ].addMouseListener(listener);

            compColumns.add( indexConstrColumns[ i ] );

            i++;
        }



        // column labels are placed in separate compartment

        compColumns.setLayoutManager( new ToolbarLayout( false ) );
        compColumns.setBorder( new SeparatorBorder() );

        add(compColumns);        

    }


    public SymbolicObject getSymbolicObject(){
        return (SymbolicArrayObject)so;
    }


    public  HashMap getIndexY(){
        HashMap result=new HashMap();
        for(int i=0;i<indexColumns.length;i++){
            Term index = indexColumns[i].getIndex();
            Rectangle bounds = indexColumns[i].getBounds().getCopy();
            int p = bounds.y+bounds.height/2-this.getBounds().y;
            result.put(index,new Integer(p));

        }

        return result;
    }

    public static void sort(IndexLabel[] a) {
        if (a == null)
            return;
        boolean sorted = false;
        IndexLabel help;
        while (!sorted) {
            sorted = true;
            for (int i = 0; i < a.length - 1; i++) {
                if (a[i].getKeY() > a[i + 1].getKeY()) {
                    help = a[i];
                    a[i] = a[i + 1];
                    a[i + 1] = help;
                    sorted = false;
                }
            }

        }
    }

    public class IndexLabel extends Figure{
        private final SymbolicArrayObject so;
        private final Term pv;
        private boolean selected=false;
        private String text;

        public IndexLabel(SymbolicArrayObject so, Term index, LinkedList sos){
            super();
            this.so = so ;
            this.pv = index;
            ToolbarLayout layout = new ToolbarLayout();
            layout.setMinorAlignment(ToolbarLayout.ALIGN_CENTER);
            layout.setVertical(false);
            layout.setStretchMinorAxis(false);
            layout.setSpacing(2);

            this.setLayoutManager(layout);


            text = VisualDebugger.getVisualDebugger().prettyPrint(SLListOfTerm.EMPTY_LIST.append(index),sos,so);
            final Label l= new Label(text);
            l.setLabelAlignment(PositionConstants.CENTER);
            this.add(l);
            l.setBorder(new LineBorder(ColorConstants.black));
            if (so.getAllPostIndex().contains(index)){
                this.add(new Label(" := "+VisualDebugger.getVisualDebugger().prettyPrint(SLListOfTerm.EMPTY_LIST.append(so.getValueTermForIndex(index)),sos,so)));
            }


            setFont( Display.getCurrent().getSystemFont() );
            l.setFont( Display.getCurrent().getSystemFont() );

        }

        public Term getIndex() {
            return pv;
        }

        private int getKeY(){
            int key=-1;
            try{                
                key =    Integer.valueOf(text.substring(0, text.length()-1)).intValue();
            }catch(NumberFormatException e){
                key = -1;             
            }
            return key;
        }

        public SymbolicArrayObject getSo() {
            return so;
        }

        public void setSelected(boolean value) {
            this.selected = value;
            if (selected)
                setForegroundColor(ColorConstants.blue);
            else
                setForegroundColor(null);
            repaint();
        }


    }



    public class IndexConstraintLabel extends Label{
        private final SymbolicArrayObject so;
        private final SetOfTerm con;
        private boolean selected=false;

        public IndexConstraintLabel(SymbolicArrayObject so, SetOfTerm index,SetOfTerm index2,LinkedList sos){
            super();           
            this.so = so ;
            this.con = index;
            String text = VisualDebugger.getVisualDebugger().prettyPrint(index2,sos,so);

            this.setText(text);
            setFont( Display.getCurrent().getSystemFont() );
        }

        public SetOfTerm getIndexConstraints() {
            return con;
        }

        public SymbolicArrayObject getSo() {
            return so;
        }

        public void setSelected(boolean value) {
            this.selected = value;
            if (selected)
                this.setForegroundColor(ColorConstants.blue);
            else
                this.setForegroundColor(null);
            repaint();
        }


    }

}
