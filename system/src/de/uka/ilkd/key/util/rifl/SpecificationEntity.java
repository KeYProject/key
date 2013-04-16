package de.uka.ilkd.key.util.rifl;

/** Program elements which may be named as sources or sinks in RIFL.
 * @author bruns
 */
public abstract class SpecificationEntity {

    public final String inPackage;
    public final String inClass;
    
    private SpecificationEntity (String p, String c) {
        inPackage = (p == null)? "" : p;
        inClass = c;
    }
    
    public abstract String qualifiedName ();
    public abstract boolean equals(Object o);

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

        @Override
        public String qualifiedName() {
            return inPackage+"."+inClass+"#"+name;
        }
    }
    
    public static class ReturnValue extends SpecificationEntity {
        
        public final String methodName;
        public final String[] paramTypes;
        
        ReturnValue (String m, String p, String c) {
            super(p,c);
            int i = m.indexOf('(');
            methodName = m.substring(0, i);
            paramTypes = m.substring(i,m.lastIndexOf(')')).split(",");
        }
        
        @Override
        public boolean equals(Object o){
            if (o instanceof ReturnValue){
                return (inPackage.equals(((ReturnValue) o).inPackage)
                        && inClass.equals(((ReturnValue) o).inClass)
                        && methodName.equals(((ReturnValue) o).methodName)
                        && paramTypes.equals(((ReturnValue) o).paramTypes));
            } else return false;
        }

        @Override
        public String qualifiedName() {
            StringBuffer sb = new StringBuffer(inPackage+"."+inClass+"#"+methodName+"(");
            for (String p: paramTypes) {
                sb.append(p);
                sb.append(',');
            }
            sb.deleteCharAt(sb.length());
            return sb.toString();
        }
    }
    
    public static class Parameter extends SpecificationEntity {

        public final String methodName;
        public final String[] paramTypes;
        public final int position;
        
        Parameter (int pos, String m, String p, String c) {
            super(p,c);
            int i = m.indexOf('(');
            methodName = m.substring(0, i);
            paramTypes = m.substring(i,m.lastIndexOf(')')).split(",");
            position = pos;
        }
        
        @Override
        public boolean equals(Object o){
            if (o instanceof Parameter) {
                return (inPackage.equals(((Parameter) o).inPackage)
                        && inClass.equals(((Parameter) o).inClass)
                        && methodName.equals(((Parameter) o).methodName)
                        && paramTypes.equals(((Parameter) o).paramTypes)
                        && position == ((Parameter)o).position);
            } return false;
        }

        @Override
        public String qualifiedName() {
            StringBuffer sb = new StringBuffer(inPackage+"."+inClass+"#"+methodName+"(");
            for (String p: paramTypes) {
                sb.append(p);
                sb.append(',');
            }
            sb.deleteCharAt(sb.length());
            return sb.toString();
        }
    }

}
