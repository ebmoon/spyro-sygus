import os
import time
from implication import ImplicationOracle

from parser import SpyroSygusParser
from synth import SynthesisOracle
from implication import ImplicationOracle
from util import *


class PropertySynthesizer:
    def __init__(self, infile, outfile, v):

        # Input/Output file stream
        self.__infile = infile
        self.__outfile = outfile
      
        # Template for Sketch synthesis
        self.__ast = SpyroSygusParser().parse(self.__infile.read())

        # Iterators
        self.__outer_iterator = 0
        self.__inner_iterator = 0

        # Primitives
        self.__synthesis_oracle = SynthesisOracle(self.__ast)
        self.__implication_oracle = ImplicationOracle(self.__ast)

        # Options
        self.__verbose = v
        self.__timeout = 300

    def __write_output(self, output):
        self.__outfile.write(output)     

    def __synthesize_stronger(self, phi_list, phi):
        if self.__verbose:
            print(f'Iteration {self.__outer_iterator} - {self.__inner_iterator}: Try synthesis') 
            self.__inner_iterator += 1

        # Run CVC5
        start_time = time.time()
        phi = self.__synthesis_oracle.synthesize_stronger(phi_list, phi)
        end_time = time.time()
        
        # Update statistics
        elapsed_time = end_time - start_time

        if self.__verbose:
            print(phi)

        # Return the result
        if phi != None:
            return phi
        else:
            return None

    def __check_improves_predicate(self, phi_list, phi):
        if self.__verbose:
            print(f'Iteration {self.__outer_iterator} : Check termination')

        # Run CVC5
        start_time = time.time()
        e_neg = self.__implication_oracle.check_implication(phi_list, phi)
        end_time = time.time()

        if self.__verbose:
            print(e_neg)

        # Statistics
        elapsed_time = end_time - start_time

        # Return the result
        return e_neg

    def __synthesize_property(self, phi_list, phi_init):
        # Assume that current phi is sound
        phi_e = phi_init
        
        while True:
            phi = self.__synthesize_stronger(phi_list, phi_e)
            if phi != None:
                phi_e = phi
            else:
                return phi_e


    def __synthesize_all_properties(self):
        phi_list = []
        pos = []

        while True:
            phi_init = self.__synthesis_oracle.synthesize_sound()
            phi = self.__synthesize_property(phi_list, phi_init)

            # Check if most precise candidates improves property. 
            # If neg_must is nonempty, those examples are witness of improvement.
            e_neg = self.__check_improves_predicate(phi_list, phi)
            if e_neg == None:
                return phi_list

            # Strengthen the found property to be most precise L-property
            phi = self.__synthesize_property([], phi)
     
            phi_list.append(phi)

            if self.__verbose:
                print("Obtained a best L-property")
                print(phi)

            self.__outer_iterator += 1
            self.__inner_iterator = 0
    
    def run(self):
        phi_list = self.__synthesize_all_properties()
        print(phi_list)