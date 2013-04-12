package de.uka.ilkd.key.util.rifl;

public abstract class SpecificationEntity {

    public final String inPackage;
    public final String inClass;
    
    private SpecificationEntity (String p, String c) {
        inPackage = p; inClass = c;
    }

    public static class Field extends SpecificationEntity {
        
        public final String name;
        
        Field (String n, String p, String c) {
            super(p,c);
            name = n;
        }
        
        @Override
        public boolean equals (Object o) {
            if (o instanceof Field) {
                return (inPackage.equals(((Field) o).inPackage)
                        && inClass.equals(((Field) o).inClass)
                        && name.equals(((Field) o).name));
            } else return false;
        }
    }
    
    public static class ReturnValue extends SpecificationEntity {
        
        public final String methodName;
        
        ReturnValue (String m, String p, String c) {
            super(p,c);
            methodName = m;
        }
        
        @Override
        public boolean equals(Object o){
            if (o instanceof ReturnValue){
                return (inPackage.equals(((ReturnValue) o).inPackage)
                        && inClass.equals(((ReturnValue) o).inClass)
                        && methodName.equals(((ReturnValue) o).methodName));
            } else return false;
        }
    }
    
    public static class Parameter extends SpecificationEntity {

        public final String methodName;
        public final int position;
        
        Parameter (int pos, String m, String p, String c) {
            super(p,c);
            methodName = m;
            position = pos;
        }
        
        @Override
        public boolean equals(Object o){
            if (o instanceof Parameter) {
                return (inPackage.equals(((Parameter) o).inPackage)
                        && inClass.equals(((Parameter) o).inClass)
                        && methodName.equals(((Parameter) o).methodName)
                        && position == ((Parameter)o).position);
            } return false;
        }
    }

}
