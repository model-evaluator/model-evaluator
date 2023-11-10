package model;

import java.util.List;

import org.javers.core.metamodel.annotation.Id;

import model.url.Domain;

public class Media {
	
	@Id
	public String name;
	
	public List<Domain> permitted;
	
	public Media(String _name) {
		this.name = _name;
	}
}
