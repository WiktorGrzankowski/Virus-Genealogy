#ifndef _VIRUS_GENEALOGY_
#define _VIRUS_GENEALOGY_

#include <map>
#include <vector>
#include <set>
#include <list>

class VirusNotFound : public std::exception {
public:
    inline const char *what() const noexcept override {
        return "VirusNotFound";
    }
};

class VirusAlreadyCreated : public std::exception {
public:
    inline const char *what() const noexcept override {
        return "VirusAlreadyCreated";
    }
};

class TriedToRemoveStemVirus : public std::exception {
public:
    inline const char *what() const noexcept override {
        return "TriedToRemoveStemVirus";
    }
};

template<typename Virus>
class VirusGenealogy {
private:
    struct set_compare {
        inline bool operator()(const Virus &a, const Virus &b) const {
            return a.get_id() > b.get_id();
        }
    };

    using children_t = std::set<typename Virus::id_type>;
    using parents_t = std::set<typename Virus::id_type>;
    using virus_set_t = std::set<Virus, set_compare>;

    class Node {
    public:
        children_t children;
        parents_t parents;
        typename Virus::id_type virus;

        Node(children_t children, parents_t parents,
             typename Virus::id_type virus)
                : children(children), parents(parents), virus(virus) {}
    };

    using graph_t = std::map<typename Virus::id_type, Node>;

    mutable graph_t graph;
    mutable virus_set_t virus_set;
    typename Virus::id_type stem_id;

    inline parents_t create_virus_set(
            std::vector<typename Virus::id_type> const &ids) {
        parents_t result;

        for (auto &id : ids)
            result.insert(graph.find(id)->second.virus);

        return result;
    }

public:
    class children_iterator {
    public:
        //Needed to satisfy bidirectional_iterator concept.
        using difference_type = std::ptrdiff_t;
        using type = Virus *;
        using value_type = typename Virus::id_type;

        inline const Virus &operator*() const {
            virus_set.insert(Virus(*children_vec_it));
            return *virus_set.find(*children_vec_it);
        }

        inline const Virus *operator->() {
            virus_set.insert(Virus(*children_vec_it));
            return &**this;
        }

        inline children_iterator &operator++() {
            ++children_vec_it;
            return *this;
        }

        inline children_iterator operator++(int) {
            auto copy = *this;
            ++children_vec_it;
            return copy;
        }

        inline children_iterator &operator--() {
            --children_vec_it;
            return *this;
        }

        inline children_iterator operator--(int) {
            auto copy = *this;
            --children_vec_it;
            return copy;
        }

        inline bool operator==(const children_iterator &other) const {
            return other.children_vec_it == children_vec_it;
        }

        inline children_iterator(typename children_t::iterator it,
                                 virus_set_t virus_set)
                : children_vec_it(it), virus_set(virus_set) {}

        inline children_iterator() = default;

    private:
        typename children_t::iterator children_vec_it;
        mutable virus_set_t virus_set;

    };

    inline VirusGenealogy<Virus>::children_iterator
    get_children_begin(typename Virus::id_type const &id) const {
        if (!exists(id))
            throw VirusNotFound();

        return children_iterator(graph.find(id)->second.children.begin(),
                                 virus_set);
    }

    inline VirusGenealogy<Virus>::children_iterator
    get_children_end(typename Virus::id_type const &id) const {
        if (!exists(id))
            throw VirusNotFound();

        return children_iterator(graph.find(id)->second.children.end(),
                                 virus_set);
    }

    // Strong guarantee is provided by working on a copy.
    inline VirusGenealogy(typename Virus::id_type const &stem_id)
            : stem_id(stem_id) {
        graph_t tmp_graph;
        tmp_graph.insert({stem_id,
                          Node(children_t(), parents_t(), stem_id)});

        std::swap(graph, tmp_graph);
    }

    inline VirusGenealogy(const VirusGenealogy &) = delete;

    inline VirusGenealogy &operator=(const VirusGenealogy &) = delete;

    //Strong guarantee, becaus comaprison of ids can throw.
    inline bool exists(typename Virus::id_type const &id) const {
        return graph.contains(id);
    }

    //Strong guarantee - does not modify anything, ctor of Virus
    //can throw exception, as well as comparison of Virus (used in find()).
    inline const Virus &operator[](typename Virus::id_type const &id) const {
        auto result = graph.find(id);
        if (result != graph.end()) {
            virus_set.insert(Virus(result->second.virus));
            return *virus_set.find(result->second.virus);
        } else
            throw VirusNotFound();
    }


    //This is strong guarantee, because only operation on original is strong
    //guarantee, and if any operation fails after it, rollback in nothrow way is
    //performed.
    inline void create(typename Virus::id_type const &id,
                       typename Virus::id_type const &parent_id) {
        if (exists(id))
            throw VirusAlreadyCreated();

        if (!exists(parent_id))
            throw VirusNotFound();

        parents_t parents;
        parents.insert(graph.find(parent_id)->second.virus);

        auto it_inserted = graph.insert(graph.end(), {id,
                                                      Node(children_t(),
                                                           parents, id)});

        try {
            auto it_parent = graph.find(parent_id);
            auto child_vector_cp = it_parent->second.children;
            child_vector_cp.insert(it_inserted->second.virus);

            //Nothrow.
            std::swap(it_parent->second.children, child_vector_cp);
        }
        catch (...) {
            //If something above threw, that means I have to only erase what
            //has been added to graph -
            //fortunately erase is nothrow if iterator is known.
            graph.erase(it_inserted);

            throw;
        }
    }

    //The same technic as above, only we need to remember changes in some way,
    //so they are saved in list because it has many nothrow operations.
    inline void create(typename Virus::id_type const &id,
                       std::vector<typename Virus::id_type> const &parent_ids) {
        if (exists(id))
            throw VirusAlreadyCreated();

        for (auto &parent_id: parent_ids)
            if (!exists(parent_id)) {
                throw VirusNotFound();
            }

        if (parent_ids.size() == 0)
            return;

        parents_t parents(create_virus_set(parent_ids));

        auto it_inserted = graph.insert(graph.end(),
                                        {id,
                                         {children_t(), parents, id}});

        std::list<children_t> sets_to_swap;
        std::list<typename graph_t::iterator> its_to_originals;

        try {
            for (auto &parent : parent_ids) {
                auto it_parent = graph.find(parent);
                auto child_vector_cp = it_parent->second.children;
                child_vector_cp.insert(it_inserted->second.virus);

                sets_to_swap.push_back(child_vector_cp);
                its_to_originals.push_back(it_parent);

                //If nothing failed, that means two lists have been created -
                //lists of modified sets and its to originals.
            }
        }
        catch (...) {
            //If something above threw, that means I have to only erase what I
            //have added to graph - fortunately erase is nothrow if iterator
            //is known (getting iterator can throw).
            graph.erase(it_inserted);

            throw;
        }

        //All below is nothrow because std::swap is, pop(), back() also.
        //operations on iterator are most likely unsafe on exceptions,
        //hence decision to use std::list has been made.
        while (!sets_to_swap.empty()) {
            std::swap(sets_to_swap.back(),
                      its_to_originals.back()->second.children);

            sets_to_swap.pop_back();
            its_to_originals.pop_back();
        }
    }

    inline typename Virus::id_type get_stem_id() const {
        return stem_id;
    }

    //This is strong guarantee.
    inline std::vector<typename Virus::id_type>
    get_parents(typename Virus::id_type const &id) const {
        if (!exists(id))
            throw VirusNotFound();

        std::vector<typename Virus::id_type> result;
        parents_t set_of_parents = graph.at(id).parents;

        for (auto &parent : set_of_parents)
            result.push_back(parent);

        return result;
    }

    //Strong guarantee, by working on copies and performing nothrow swaps later.
    inline void connect(typename Virus::id_type const &child_id,
                        typename Virus::id_type const &parent_id) {
        if (!exists(child_id) || !exists(parent_id))
            throw VirusNotFound();

        auto child_node = graph.find(child_id);
        auto parent_node = graph.find(parent_id);

        //The task does not allow multiverticies.
        if (!(child_node->second.parents.contains(parent_id))) {
            auto child_parents_cp = child_node->second.parents;
            auto parent_children_cp = parent_node->second.children;

            //We have to tell child that it has new parent,
            //and we have to tell parent that it has new child.
            child_parents_cp.insert(parent_node->second.virus);
            parent_children_cp.insert(child_node->second.virus);

            //Nothrow.
            std::swap(child_node->second.parents, child_parents_cp);
            std::swap(parent_node->second.children, parent_children_cp);
        }
    }

    //Strong guarantee, because all operations are performed on copies.
    inline graph_t
    remove_helper(graph_t copied_graph, typename Virus::id_type const &id) {
        auto children_set_copy = copied_graph.at(id).children;

        auto it = copied_graph.at(id).parents.begin();
        while (it != copied_graph.at(id).parents.end()) {
            copied_graph.at((*it)).children.erase(graph.at(id).virus);
            it++;
        }

        it = children_set_copy.begin();
        while (it != children_set_copy.end()) {
            if (copied_graph.at(*it).parents.size() == 1) {
                auto tmp = remove_helper(copied_graph, *it);
                swap(copied_graph, tmp);
            } else {
                copied_graph.at((*it)).parents.erase(
                        graph.at(id).virus);
            }
            ++it;
        }
        copied_graph.erase(id);
        return copied_graph;
    }

    //This is strong guarantee, because all of the work is done on copy and swap
    //is performed later. It cannot be done without copying, because nothrow
    //rollback is not possible.
    inline void remove(typename Virus::id_type const &id) {
        if (!exists(id))
            throw VirusNotFound();

        if (id == stem_id)
            throw TriedToRemoveStemVirus();

        auto copied_graph = graph;
        auto tmp = remove_helper(copied_graph, id);
        std::swap(graph, tmp);
    }
};

#endif
