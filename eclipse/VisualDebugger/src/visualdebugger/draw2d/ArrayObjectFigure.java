package visualdebugger.draw2d;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;

import org.eclipse.draw2d.*;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.swt.widgets.Display;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;
import de.uka.ilkd.key.visualdebugger.statevisualisation.SymbolicArrayObject;
import de.uka.ilkd.key.visualdebugger.statevisualisation.SymbolicObject;
import de.uka.ilkd.key.visualdebugger.statevisualisation.SymbolicObjectDiagram;

public class ArrayObjectFigure extends ObjectFigure {

    private final IndexLabel[] indexColumns;


    private Label[] indexConstrColumns;

    private LinkedList<SymbolicObject> sos;

    public ArrayObjectFigure(SymbolicArrayObject sao, MouseListener listener,
            SymbolicObjectDiagram symbState,boolean pre) {
        super(sao, listener, symbState,pre);        
        this.sos = symbState.getSymbolicObjects();
        createConstr(listener);
        ImmutableSet<Term> indexes = sao.getAllIndexTerms();
        indexes=indexes.union(sao.getAllPostIndex());

        indexColumns = new IndexLabel[ indexes.size()];
        final IFigure compColumns = new Figure();
        int i =0;
        for(Iterator<Term> it=indexes.iterator();it.hasNext();){
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


    private ImmutableSet<Term> disj(ImmutableSet<Term> s1, ImmutableSet<Term> s2){
        ImmutableSet<Term> result = DefaultImmutableSet.<Term>nil();
        for(Iterator<Term> it=s1.iterator();it.hasNext();){
            Term t = it.next();
            if(s2.contains(t))
                result=result.add(t);
        }
        return result;

    }


    private ImmutableSet<Term> exclude(ImmutableSet<Term> s1, ImmutableSet<Term> s2){
        ImmutableSet<Term> result = s1;
        for(Iterator<Term> it=s2.iterator();it.hasNext();){
            Term t = it.next();
            if(s1.contains(t))
                result=result.remove(t);
        }
        return result;

    }



    private void createConstr(MouseListener listener) {
        LinkedList<ImmutableSet<Term>> indexTermPos = 
            ((SymbolicArrayObject)this.getSymbolicObject()).
            getPossibleIndexTermConfigurations();
        if (indexTermPos.size()<=1)
            return;
        ImmutableSet<Term> cut= DefaultImmutableSet.<Term>nil();
        if (indexTermPos.size()>0){
            Iterator<ImmutableSet<Term>> it = indexTermPos.iterator();
            cut = it.next();
            while(it.hasNext()){
                cut = disj(cut, it.next());
            }
        }



        //  System.out.println("Indizes "+attributes);
        indexConstrColumns = new Label[ indexTermPos.size()];
        final IFigure compColumns = new Figure();
        int i =0;
        for(Iterator<ImmutableSet<Term>> it=indexTermPos.iterator();it.hasNext();){

            final ImmutableSet<Term> indexConstr = it.next();
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


    public  HashMap<Term, Integer> getIndexY(){
        HashMap<Term, Integer> result=new HashMap<Term, Integer>();
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

        public IndexLabel(SymbolicArrayObject so, Term index, LinkedList<SymbolicObject> sos){
            super();
            this.so = so ;
            this.pv = index;
            ToolbarLayout layout = new ToolbarLayout();
            layout.setMinorAlignment(ToolbarLayout.ALIGN_CENTER);
            layout.setVertical(false);
            layout.setStretchMinorAxis(false);
            layout.setSpacing(2);

            this.setLayoutManager(layout);


            text = VisualDebugger.getVisualDebugger().prettyPrint(ImmutableSLList.<Term>nil().append(index),sos,so);
            final Label l= new Label(text);
            l.setLabelAlignment(PositionConstants.CENTER);
            this.add(l);
            l.setBorder(new LineBorder(ColorConstants.black));
            if (so.getAllPostIndex().contains(index)){
                this.add(new Label(" := "+VisualDebugger.getVisualDebugger().prettyPrint(ImmutableSLList.<Term>nil().append(so.getValueTermForIndex(index)),sos,so)));
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
        private final ImmutableSet<Term> con;
        private boolean selected=false;

        public IndexConstraintLabel(SymbolicArrayObject so, ImmutableSet<Term> index,ImmutableSet<Term> index2,LinkedList<SymbolicObject> sos){
            super();           
            this.so = so ;
            this.con = index;
            String text = VisualDebugger.getVisualDebugger().prettyPrint(index2,sos,so);

            this.setText(text);
            setFont( Display.getCurrent().getSystemFont() );
        }

        public ImmutableSet<Term> getIndexConstraints() {
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
