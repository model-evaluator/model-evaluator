package model.url;

public class BlobNoPathUrl extends Url {
	
	
	public BlobNoPathUrl(String name) {
		super(name);
		this.scheme = Scheme.Blob;
		this.corresponding = "blob://";
		this.correspondingOrigin = "BlankOrigin";
	}

}
