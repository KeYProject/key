package de.uka.ilkd.key.util.rifl;

/** Program elements which may be named as sources or sinks in RIFL.
 * @author bruns
 */
public abstract class SpecificationEntity {

    public final String inPackage;
    public final String inClass;
    
    private SpecificationEntity (String p, String c) {
        inPackage = (p == null)? "" : p.intern();
        inClass = c.intern();
    }
    
    @Override
    public String toString() {
        return qualifiedName();
    }
    
    public abstract String qualifiedName ();
    
    @Override
    public abstract boolean equals(Object o);
    
    @Override
    public abstract int hashCode();
    
    ////////////////////////////////////////////////////
    // implementations
    ////////////////////////////////////////////////////

    public static final class Field extends SpecificationEntity {
        
        public final String name;
        
        Field (String n, String p, String c) {
            super(p,c);
            name = n.intern();
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
            return (inPackage == ""? "": inPackage+".")+inClass+"#"+name;
        }

        @Override
        public int hashCode() {
            return 3976*(inPackage+inClass).hashCode() + name.hashCode();  
        }
    }
    
    public static final class ReturnValue extends SpecificationEntity {
        
        public final String methodName;
        public final String[] paramTypes;
        
        ReturnValue (String m, String p, String c) {
            super(p,c);
            int i = m.indexOf('(');
            methodName = m.substring(0, i).intern();
            paramTypes = m.substring(i+1,m.lastIndexOf(')')).split(",");
        }
        
        ReturnValue (String m, String[] pt, String p, String c) {
            super(p,c);
            methodName = m;
            paramTypes = pt;
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
            StringBuffer sb = new StringBuffer();
            if (!"".equals(inPackage))
                sb.append(inPackage+".");
            sb.append(inClass+"#"+methodName+"(");
            for (String p: paramTypes) {
                sb.append(p);
                sb.append(',');
            }
            sb.deleteCharAt(sb.length());
            return sb.toString();
        }

        @Override
        public int hashCode() {
            return 3722 * (inPackage+inClass).hashCode()
                    + 76 * methodName.hashCode() + paramTypes.hashCode();
        }
    }
    
    public static final class Parameter extends SpecificationEntity {

        public final String methodName;
        public final String[] paramTypes;
        public final int position;
        
        Parameter (int pos, String m, String p, String c) {
            super(p,c);
            int i = m.indexOf('(');
            methodName = m.substring(0, i).intern();
            paramTypes = m.substring(i+1,m.lastIndexOf(')')).split(",");
            position = pos;
        }
        
        Parameter(int pos, String m, String[] pt, String p, String c){
            super(p,c);
            position = pos;
            methodName = m;
            paramTypes = pt;
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
            StringBuffer sb = new StringBuffer();
            if (!"".equals(inPackage))
                sb.append(inPackage+".");
            sb.append(inClass+"#"+methodName+"(");
            for (String p: paramTypes) {
                sb.append(p);
                sb.append(',');
            }
            sb.deleteCharAt(sb.length());
            return sb.toString();
        }

        @Override
        public int hashCode() {
            return 3668 * (inPackage+inClass).hashCode()
                    + 46 * (methodName.hashCode() + paramTypes.hashCode())
                    + position;
        }
    }

}
