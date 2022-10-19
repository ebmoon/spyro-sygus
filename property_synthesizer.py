import os
import time
from implication import ImplicationOracle

from parser import SpyroSygusParser
from synth import SynthesisOracle
from soundness import SoundnessOracle
from precision import PrecisionOracle
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
        self.__soundness_oracle = SoundnessOracle(self.__ast)
        self.__precision_oracle = PrecisionOracle(self.__ast)
        self.__implication_oracle = ImplicationOracle(self.__ast)

        # Options
        self.__verbose = v
        self.__timeout = 300

    def __write_output(self, output):
        self.__outfile.write(output)     

    def __synthesize(self, pos, neg_must, neg_may, check_realizable = True):
        if self.__verbose:
            print(f'Iteration {self.__outer_iterator} - {self.__inner_iterator}: Try synthesis') 
            self.__inner_iterator += 1

        # Run CVC5
        start_time = time.time()
        phi = self.__synthesis_oracle.synthesize(pos, neg_must + neg_may, check_realizable)
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

    def __check_soundness(self, phi):
        if self.__verbose:
            print(f'Iteration {self.__outer_iterator} - {self.__inner_iterator}: Check soundness')
            self.__inner_iterator += 1

        # Run CVC5
        start_time = time.time()
        e_pos = self.__soundness_oracle.check_soundness(phi)
        end_time = time.time()

        # Statistics
        elapsed_time = end_time - start_time

        if self.__verbose:
            print(e_pos)

        # Return the result
        if e_pos != None:
            self.__synthesis_oracle.add_positive_example(e_pos)
            return (e_pos, False)
        else:
            return (None, elapsed_time >= self.__timeout)

    def __check_precision(self, phi_list, phi, pos, neg_must, neg_may):
        if self.__verbose:
            print(f'Iteration {self.__outer_iterator} - {self.__inner_iterator}: Check precision')
            self.__inner_iterator += 1

        # Run CVC5
        start_time = time.time()
        e_neg = self.__precision_oracle.check_precision(phi_list, phi, pos, neg_must + neg_may)
        end_time = time.time()

        # Update statistics
        elapsed_time = end_time - start_time

        if self.__verbose:
            print(e_neg)

        # Return the result
        if e_neg != None:
            self.__synthesis_oracle.add_negative_example(e_neg)
            return e_neg
        else:
            self.__time_last_query = elapsed_time
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

    def __add_new_sound_property(self, phi_list, phi):
        phi_list_new = []
        for phi_old in phi_list:
            if self.__implication_oracle.check_implication([phi], phi_old) != None:
                phi_list_new.append(phi_old)

        return phi_list_new + [phi]

    def __synthesize_property(self, phi_list, phi_init, pos, neg_must, best = False):
        # Assume that current phi is sound
        phi_e = phi_init
        phi_last_sound = None
        neg_may = []
        phi_sound = []

        while True:
            e_pos, timeout = self.__check_soundness(phi_e)
            if e_pos != None:
                pos.append(e_pos)
                
                # First try synthesis
                phi = self.__synthesize(pos, neg_must, neg_may)

                # If neg_may is a singleton set, it doesn't need to call MaxSynth
                # Revert back to the last sound property we found
                if phi == None and len(neg_may) == 1 and phi_last_sound != None:
                    phi = phi_last_sound
                    neg_may = []
                    
                    self.__synthesis_oracle.clear_negative_may()

                # MaxSynth is not implemented currently, and this should not be happened
                elif phi == None:
                    raise NotImplementedError

                phi_e = phi
         
            # Return the last sound property found
            elif timeout and phi_last_sound != None:
                return (phi_last_sound, pos, neg_must + neg_may)
            
            # Check precision after pass soundness check
            else:
                phi_last_sound = phi_e    # Remember the last sound property
                phi_sound = self.__add_new_sound_property(phi_sound, phi_e)

                # If phi_e is phi_truth, which is initial candidate of the first call,
                # then phi_e doesn't rejects examples in neg_may. 
                neg_must += neg_may
                neg_may = []
                
                self.__synthesis_oracle.freeze_negative_example()

                phi_precision = [phi_e] if best else phi_list + phi_sound 
                e_neg = self.__check_precision(phi_precision, phi_e, pos, neg_must, neg_may)
                if e_neg != None:   # Not precise
                    neg_may.append(e_neg)
                    phi_e = self.__synthesize(pos, neg_must, neg_may, False)
                else:                               # Sound and Precise
                    return (phi_e, pos, neg_must)

    def __synthesize_all_properties(self):
        phi_list = []
        pos = []

        while True:
            phi_init = self.__synthesize(pos, [], [])
            phi, pos, neg_must = self.__synthesize_property(phi_list, phi_init, pos, [], False)

            # Check if most precise candidates improves property. 
            # If neg_must is nonempty, those examples are witness of improvement.
            if len(neg_must) == 0:
                e_neg = self.__check_improves_predicate(phi_list, phi)
                if e_neg != None:
                    neg_must = [e_neg]
                    self.__synthesis_oracle.add_negative_example(e_neg)
                    self.__synthesis_oracle.freeze_negative_example()
                else:            
                    return phi_list

            # Strengthen the found property to be most precise L-property
            phi, pos, _ = self.__synthesize_property([], phi, pos, neg_must, True)
     
            phi_list.append(phi)

            self.__synthesis_oracle.clear_negative_example()

            if self.__verbose:
                print("Obtained a best L-property")
                print(phi)

            self.__outer_iterator += 1
            self.__inner_iterator = 0
    
    def run(self):
        phi_list = self.__synthesize_all_properties()
        print(phi_list)