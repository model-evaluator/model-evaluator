package model.url;

import org.javers.core.metamodel.annotation.Id;

public class TupleOrigin extends Origin {
	
	@Id
	public String name;
	
	public Scheme scheme;
	
	public Domain hostName;
	
	public TupleOrigin(String _name) {
		this.name = _name;
		this.originStr = "TupleOrigin";
	}
	
	public TupleOrigin() {
		this.originStr = "TupleOrigin";
	}
	
	
	@Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }

        if (obj.getClass() != this.getClass()) {
            return false;
        }

        final TupleOrigin other = (TupleOrigin) obj;
        if ((this.hostName == null) ? (other.hostName != null) : !this.hostName.equals(other.hostName)) {
            return false;
        }

        if (this.scheme != other.scheme) {
            return false;
        }
        /*if (!this.hostName.equals(other.hostName)) {
        	return false;
        }*/

        return true;
    }

}
