package hu.bme.mit.inf.ttmc.system.ui;

import java.io.IOException;
import java.util.Collections;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.xtext.resource.XtextResource;
import org.eclipse.xtext.resource.XtextResourceSet;

import com.google.inject.Inject;
import com.google.inject.Injector;

import hu.bme.mit.inf.ttmc.system.language.SystemLanguageStandaloneSetup;
import hu.bme.mit.inf.ttmc.system.model.SystemModelPackage;
import hu.bme.mit.inf.ttmc.system.model.SystemSpecification;


public class SystemModelLoader {

	private static SystemModelLoader instance;

	@Inject
	private XtextResourceSet resourceSet;

	private SystemModelLoader() {
		final SystemLanguageStandaloneSetup setup = new SystemLanguageStandaloneSetup();
		final Injector injector = setup.createInjectorAndDoEMFRegistration();
		SystemModelPackage.eINSTANCE.eClass();
		injector.injectMembers(this);
		resourceSet.addLoadOption(XtextResource.OPTION_RESOLVE_ALL, Boolean.TRUE);
	}

	public static SystemModelLoader getInstance() {
		if (instance == null) {
			instance = new SystemModelLoader();
		}
		return instance;
	}

	public SystemSpecification load(String fileName) {
		final URI uri = URI.createFileURI(fileName);
		final Resource resource = resourceSet.getResource(uri, true);
		final EObject object = resource.getContents().get(0);
		final SystemSpecification specification = (SystemSpecification) object;
		return specification;
	}

	public void save(SystemSpecification specification, String fileName) throws IOException {
		final URI uri = URI.createFileURI(fileName);
		final Resource resource = resourceSet.createResource(uri);
		resource.getContents().add(specification);
       	resource.save(Collections.EMPTY_MAP);
    }
}
