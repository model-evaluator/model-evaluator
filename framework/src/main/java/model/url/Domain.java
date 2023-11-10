package model.url;

public class Domain {
	
	public String name;
	
	public Domain(String _name) {
		this.name = _name;
	}
	
	
	@Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }

        if (obj.getClass() != this.getClass()) {
            return false;
        }

        final Domain other = (Domain) obj;
        if ((this.name == null) ? (other.name != null) : !this.name.equals(other.name)) {
            return false;
        }

        return true;
    }

}
