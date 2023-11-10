package model.url;

import org.javers.core.metamodel.annotation.Id;

public class Url {
	
	@Id
	public String name;
	
	public Scheme scheme;
	
	public String corresponding;
	
	public String correspondingOrigin;
	
	public Url(String _name) {
		this.name = _name;
	}

}
