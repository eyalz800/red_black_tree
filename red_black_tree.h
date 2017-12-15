#pragma once
#include <cstddef>
#include <type_traits>
#include <stdexcept>
#include <memory>
#include <utility>
#include <functional>
#include <algorithm>
#include <iterator>
#include <initializer_list>

namespace zpp
{

/**
 * Represents a red black tree.
 */
template <typename Type,
    typename Compare = std::less<>>
class red_black_tree
{
private:
    /**
     * Represents a tree node, whose color is either red or black.
     */
    class node;

public:
    /**
     * @name Assertions regarding the tree element type.
     * @{
     */
    static_assert(!std::is_reference<Type>::value,
        "Tree cannot contain references.");

    static_assert(std::is_nothrow_move_constructible<Type>::value,
        "Must not throw on move construction.");

    static_assert(std::is_nothrow_move_assignable<Type>::value,
        "Must not throw on move assignment.");
    /*
     * @}
     */

    /**
     * @name Types used in the tree.
     * @{
     */
    using key_type = Type;
    using value_type = Type;
    using const_value_type = std::add_const_t<Type>;
    using reference = std::add_lvalue_reference_t<value_type>;
    using const_reference = std::add_lvalue_reference_t<std::add_const_t<value_type>>;
    using pointer = std::add_pointer_t<value_type>;
    using const_pointer = std::add_pointer_t<std::add_const_t<value_type>>;
    class iterator;
    using const_iterator = iterator;
    using reverse_iterator = std::reverse_iterator<iterator>;
    using const_reverse_iterator = std::reverse_iterator<const_iterator>;
    using key_compare = Compare;
    using value_compare = Compare;
    using difference_type = std::ptrdiff_t;
    using size_type = std::size_t;
    /*
     * @}
     */

    /**
     * Iterator for iterating over the tree.
     */
    class iterator
    {
        friend red_black_tree;

    public:
        /**
         * @name Types required for iterator.
         * @{
         */
        using difference_type = typename red_black_tree::difference_type;
        using value_type = typename red_black_tree::const_value_type;
        using pointer = typename red_black_tree::const_pointer;
        using reference = typename red_black_tree::const_reference;
        using iterator_category = std::bidirectional_iterator_tag;
        /*
         * @}
         */

        /**
         * Create an empty iterator.
         */
        iterator() = default;

        /**
         * Create an iterator that iterates the tree from the
         * given node.
         */
        explicit iterator(node * current_node) :
            m_node(current_node)
        {
        }

        /**
         * Advances the iterator to the next node.
         */
        iterator operator++()
        {
            // If we reached the end.
            if (nullptr == m_node) {
                m_node = m_previous_node;
                return *this;
            }

            // Save the current node as the previous node.
            m_previous_node = m_node;

            // If the current node has a right child, advance to 
            // the left most node of the right subtree.
            if (m_node->get_right()) {
                m_node = get_left_most(m_node->get_right());
                return *this;
            }

            // While the current node is a right child.
            while (m_node->is_right_child()) {
                // Advance to the parent.
                m_node = m_node->get_parent();
            }

            // If the current node is not the root node,
            // the next node is the parent node.
            if (!m_node->is_root()) {
                // Advance to the parent node.
                m_node = m_node->get_parent();
                return *this;
            }

            // There is no next value.
            m_node = nullptr;
            return *this;
        }

        /**
         * Advances the iterator to the previous node.
         */
        iterator operator--()
        {
            // If we reached the end.
            if (nullptr == m_node) {
                m_node = m_previous_node;
                return *this;
            }

            // Save the current node as the previous node.
            m_previous_node = m_node;

            // If the current node has a left child, advance to 
            // the right most node of the left subtree.
            if (m_node->get_left()) {
                m_node = get_right_most(m_node->get_left());
                return *this;
            }

            // While the current node is a left child.
            while (m_node->is_left_child()) {
                // Advance to the parent.
                m_node = m_node->get_parent();
            }

            // If the current node is not the root node,
            // the next node is the parent node.
            if (!m_node->is_root()) {
                // Advance to the parent node.
                m_node = m_node->get_parent();
                return *this;
            }

            // There is no next value.
            m_node = nullptr;
            return *this;
        }

        /**
         * Get the value of the current node.
         */
        reference operator*() const
        {
            // Return the value of the current node.
            return m_node->get_value();
        }

        /**
         * Returns true if the iterators point to the same nodes, else false.
         */
        bool operator==(const iterator & other) const
        {
            return (m_node == other.m_node);
        }

        /**
         * Returns true if the iterators point to different nodes, else false.
         */
        bool operator!=(const iterator & other) const
        {
            return (m_node != other.m_node);
        }

        /**
         * Swaps this iterator with other.
         */
        void swap(iterator & other) noexcept
        {
            std::swap(m_node, other.m_node);
            std::swap(m_previous_node, other.m_previous_node);
        }

    private:
        /**
         * Returns the current node.
         */
        node * get_node() const 
        {
            return m_node;
        }

    private:
        /**
         * The current node.
         */
        node * m_node = nullptr;

        /**
         * The previous node.
         */
        mutable node * m_previous_node = nullptr;
    };

private:
    /**
     * Represents a tree node, whose color is either red or black.
     */
    class node
    {
    public:
        friend red_black_tree;

        /**
         * The color of the node.
         */
        enum class color : std::uint8_t { red, black };

        /**
         * Constructs an empty node.
         */
        node() = default;

        /**
         * Constructs a node given a value.
         * The color will be black.
         * The node will be a non-root node, with no parent.
         */
        node(value_type value) :
            m_value(std::move(value))
        {
        }

        /**
         * Returns the value stored in the node.
         */
        const_reference get_value() const
        {
            return m_value;
        }

        /**
         * Returns the color of the node.
         */
        color get_color() const
        {
            return m_color;
        }

        /**
         * Returns the parent of the node.
         */
        node * get_parent()
        {
            if (is_root()) {
                return nullptr;
            }

            return m_parent;
        }

        /**
         * Returns the parent of the node.
         */
        const node * get_parent() const
        {
            if (is_root()) {
                return nullptr;
            }

            return m_parent;
        }

        /**
         * Sets a left child for this node.
         * In case of null - this node will have no left child.
         */
        void set_left(std::unique_ptr<node> left)
        {
            m_left = std::move(left);

            if (m_left) {
                m_left->set_parent(this);
            }
        }

        /**
         * Sets a right child for this node.
         * In case of null - this node will have no right child.
         */
        void set_right(std::unique_ptr<node> right)
        {
            m_right = std::move(right);

            if (m_right) {
                m_right->set_parent(this);
            }
        }

        /**
         * Returns the left child of this node.
         * If there is no left child, null is returned.
         */
        node * get_left()
        {
            return m_left.get();
        }

        /**
         * Returns the left child of this node.
         * If there is no left child, null is returned.
         */
        const node * get_left() const
        {
            return m_left.get();
        }

        /**
         * Returns the right child of this node.
         * If there is no right child, null is returned.
         */
        node * get_right()
        {
            return m_right.get();
        }

        /**
         * Returns the right child of this node.
         * If there is no right child, null is returned.
         */
        const node * get_right() const
        {
            return m_right.get();
        }

        /**
         * Returns true if this node is a root node, that is,
         * it was marked as root and it has an owner, else - returns false.
         */
        bool is_root() const
        {
            return m_is_root;
        }

        /**
         * Returns true if this node is a leaf node, else false.
         */
        bool is_leaf() const
        {
            return ((!m_left) && (!m_right));
        }

        /**
         * Returns true if this node is a left child of another node.
         */
        bool is_left_child() const
        {
            if (is_root() || !m_parent) {
                return false;
            }

            return (get_parent()->get_left() == this);
        }

        /**
         * Returns true if this node is a right child of another node.
         */
        bool is_right_child() const
        {
            if (is_root() || !m_parent) {
                return false;
            }

            return (get_parent()->get_right() == this);
        }

        /**
         * Performs a left rotate on the given node.
         * The node must have a right child for this operation.
         */
        void rotate_left()
        {
            // Rotate left operation requires the node to have a right child.
            if (!get_right()) {
                throw std::logic_error("Rotate left on a node requires a right child.");
            }

            // Save the owner.
            auto owner = get_owner();

            // Let the owner own the right child, and gain ownership on self.
            auto self = owner.exchange(move_right());

            // Set the right child to be the owner's left child.
            self->set_right(owner->move_left());

            // Set the owner's left child to be self.
            owner->set_left(std::move(self));
        }

        /**
         * Performs a right rotate on the given node.
         * The node must have a left child for this operation.
         */
        void rotate_right()
        {
            // Rotate right operation requires the node to have a left child.
            if (!get_left()) {
                throw std::logic_error("Rotate right on a node requires a left child.");
            }

            // Save the owner.
            auto owner = get_owner();

            // Let the owner own the left child, and gain ownership on self.
            auto self = owner.exchange(move_left());

            // Set the left child to be the owner's right child.
            self->set_left(owner->move_right());

            // Set the owner's right child to be self.
            owner->set_right(std::move(self));
        }

        /**
         * Returns true if the left color is the given color, else, false.
         * Note: null nodes are referred to as black nodes.
         */
        bool is_left_color(color value) const
        {
            // If this node has no left child.
            if (!get_left()) {
                return (color::black == value);
            }
            
            return (get_left()->get_color() == value);
        }

        /**
         * Returns true if the right color is the given color, else, false.
         * Note: null nodes are referred to as black nodes.
         */
        bool is_right_color(color value) const
        {
            // If this node has no right child.
            if (!get_right()) {
                return (color::black == value);
            }
            
            return (get_right()->get_color() == value);
        }

    private:
        /**
         * Represents a view of an owned node, that is, the node owner and
         * it's parent.
         */
        class owner_view
        {
        public:
            /**
             * Constructs an owner view from a node and its parent.
             */
            owner_view(std::unique_ptr<node> & owner, node * parent) :
                m_owner(owner),
                m_parent(parent)
            {
            }

            /**
             * Exchanges tree ownership between 'other' and the owned node.
             */
            std::unique_ptr<node> exchange(std::unique_ptr<node> other)
            {
                // Perform the transfer of ownership.
                m_owner.swap(other);

                // If the owner is not set to null, return.
                if (!m_owner) {
                    return other;
                }

                // If the previous node had a parent, update it, else,
                // mark is as a root node.
                if (m_parent) {
                    m_owner->set_parent(m_parent);
                } else {
                    m_owner->mark_as_root(m_owner);
                }

                // Return the previously owned node.
                return other;
            }

            /**
             * Returns a pointer to the owned node.
             */
            node * operator->()
            {
                return m_owner.get();
            }

        private:
            /**
             * The owned node.
             */
            std::unique_ptr<node> & m_owner;

            /**
             * Its parent.
             */
            node * m_parent = nullptr;
        };

        /**
         * This overload prevents setting parent to a nullptr.
         */
        void set_parent(std::nullptr_t) = delete;

        /**
         * Sets the parent of the current node.
         * Marks the node as a non-root node.
         */
        void set_parent(node * parent)
        {
            if (nullptr == parent) {
                throw std::logic_error("Parent cannot be set to nullptr, use set_root(...)");
            }

            m_parent = parent;
            m_is_root = false;
        }

        /**
         * Marks the current node as a root node.
         * Sets the owner of the node.
         * Changes the node color to black.
         */
        void mark_as_root(std::unique_ptr<node> & owner)
        {
            m_owner = &owner;
            m_color = color::black;
            m_is_root = true;
        }

        /**
         * Sets the color of the node.
         */
        void set_color(color color)
        {
            m_color = color;
        }

        /**
         * Transfer ownership of the left child.
         */
        std::unique_ptr<node> && move_left()
        {
            return std::move(m_left);
        }

        /**
         * Transfer ownership of the right child.
         */
        std::unique_ptr<node> && move_right()
        {
            return std::move(m_right);
        }

        /**
         * Returns the owner view of the node.
         * The owner is the unique_ptr that holds the current node, which is either
         * a subobject of a node or the unique_ptr held by the tree.
         * The owner view of the node allows exchanging the current node with another.
         */
        owner_view get_owner()
        {
            if (is_left_child()) {
                return{ m_parent->m_left, m_parent };
            }

            if (is_right_child()) {
                return{ m_parent->m_right, m_parent };
            }

            return{ *m_owner, nullptr };
        }

    private:
        /**
         * The value held in this node.
         */
        value_type m_value{};

        /**
         * The left subtree owned by this node.
         */
        std::unique_ptr<node> m_left;

        /**
         * The right subtree owned by this node.
         */
        std::unique_ptr<node> m_right;

        union
        {
            /**
             * The parent node, this member is active when 'm_is_root' is false.
             */
            node * m_parent = nullptr;

            /**
             * The owner of this node, this member is active when 'm_is_root' is true.
             */
            std::unique_ptr<node> * m_owner;
        };

        /**
         * The color of the node.
         */
        color m_color = color::black;

        /**
         * Set to true if the node is the root node, else false.
         */
        bool m_is_root = false;
    };

public:
    /**
     * Constructs an empty red black tree.
     */
    red_black_tree() = default;

    /**
     * Construct a tree with the elements in the range [first, last).
     */
    template <typename InputIterator>
    red_black_tree(InputIterator first, InputIterator last)
    {
        insert(first, last);
    }

    /**
     * Construct a red black tree with initial values.
     */
    red_black_tree(std::initializer_list<value_type> values) :
        red_black_tree(values.begin(), values.end())
    {
    }

    /**
     * Move construct a red black tree from other.
     * A moved-from tree can only be assigned to, swapped, and destroyed.
     */
    red_black_tree(red_black_tree && other) noexcept :
        m_root(std::move(other.m_root)),
        m_size(other.m_size),
		m_left_most(other.m_left_most),
		m_right_most(other.m_right_most)
    {
        other.m_size = 0;
		other.m_left_most = nullptr;
		other.m_right_most = nullptr;
    }

    /**
     * Copy constructs a red black tree from other.
     */
    red_black_tree(const red_black_tree & other) :
        m_root(std::make_unique<std::unique_ptr<node>>(clone(other.m_root->get()))),
        m_size(other.m_size)
    {
        get_root()->mark_as_root(*m_root);

        // If there is no root.
        if (!(*m_root)) {
            return;
        }

        // Update left and right most.
        m_left_most = get_left_most(m_root->get());
        m_right_most = get_right_most(m_root->get());
    }

    /**
     * Assigns other tree to this tree.
     */
    red_black_tree & operator=(red_black_tree other) noexcept
    {
        other.swap(*this);
        return *this;
    }

    /**
     * Destructs the tree.
     * The implicitly-defined destructor would have destroyed the tree recursively.
     * This destructor destroys the tree iteratively as an optimization.
     */
    ~red_black_tree()
    {
        clear();
    }

    /**
     * Clears the tree iteratively.
     */
    void clear()
    {
        // If there is no root, return.
        if (!m_root) {
            return;
        }

        // Obtain the root node.
        auto current = std::move(*m_root);

        // While the current node is valid.
        while (current) {
            // If there is a left node.
            if (current->get_left()) {
                auto left = current->move_left();
                left->set_right(current->move_right());
                current = std::move(left);
                continue;
            }

            // If there is a right node.
            if (current->get_right()) {
                auto right = current->move_right();
                right->set_left(current->move_left());
                current = std::move(right);
                continue;
            }

            // Destroy current.
            current = nullptr;
        }
    }

    /**
     * Swaps this tree with other tree.
     */
    void swap(red_black_tree & other) noexcept
    {
        using std::swap;
        swap(m_root, other.m_root);
        swap(m_size, other.m_size);
    }

    /**
     * Inserts the elements in the range [first, last) to the tree.
     */
    template <typename InputIterator>
    void insert(InputIterator first, InputIterator last)
    {
        std::for_each(first, last, [this](const auto & value) { insert(value); });
    }

    /**
     * Inserts a given value to the tree.
     */
    void insert(value_type value)
    {
        insert_node(std::make_unique<node>(std::move(value)));
        ++m_size;
    }

    /**
     * Emplace a given value to the tree.
     */
    template <typename... Arguments>
    void emplace(Arguments && ... arguments)
    {
        insert_node(std::make_unique<node>(std::forward<Arguments>(arguments)...));
        ++m_size;
    }

    /**
     * Finds an occurrence of a given value in the tree.
     * If no occurrence was found - returns the end of the tree.
     */
    const_iterator find(const_reference value) const
    {
        // Start searching from the root.
        auto current_node = get_root();

        // While the current node is valid.
        while (current_node) {
            // If the given value comes before the value in the current node.
            if (comes_before(value, current_node->get_value())) {

                // If the value in the current node also comes before the given value.
                if (comes_before(current_node->get_value(), value)) {
                    return const_iterator(current_node);
                }

                // Advance to the left side of the tree.
                current_node = current_node->get_left();
                continue;
            }

            // The given value comes does not come before the value in the current node.
            
            // If the value in the current node also does not come before value.
            if (!comes_before(current_node->get_value(), value)) {
                return const_iterator(current_node);
            }

            // The value comes after the value in the current node.
            current_node = current_node->get_right();
        }

        // Return the end of the tree.
        return cend();
    }

    /**
     * Erase all occurrences of a given value.
     */
    void erase(const_reference value)
    {
        while (true) {
            // Find the value.
            auto it = find(value);

            // If not found.
            if (end() == it) {
                return;
            }

            // Erase the value.
            erase(it);
        }
    }

    /**
     * Erase an occurrence of a given value from the tree.
     */
    void erase_one(const_reference value)
    {
        // Find the value.
        auto it = find(value);

        // If not found.
        if (end() == it) {
            return;
        }

        // Erase the value.
        erase(it);
    }

    /**
     * Erase a given value from the tree, by iterator.
     */
    void erase(iterator to_erase)
    {
        // Fetch the node to erase.
        auto node_to_erase = to_erase.get_node();

        // If the node to erase is left most, update the left most node.
        if (node_to_erase == m_left_most) {
            m_left_most = (++iterator(to_erase)).get_node();
        }

        // If the node to erase is right most, update the right most node.
        if (node_to_erase == m_right_most) {
            m_right_most = (--iterator(to_erase)).get_node();
        }
        
        // Generic node pointers that serve us in this method.
        auto owned_x = std::unique_ptr<node>();
        auto owned_y = std::unique_ptr<node>();
        auto x = static_cast<node *>(nullptr);
        auto y = static_cast<node *>(nullptr);
        
        // If the node to erase has two children.
        if (node_to_erase->get_left() && node_to_erase->get_right()) {
            // let 'y' be the node after the node to erase.
            y = (++iterator(to_erase)).get_node(); 
        } else {
            // Let 'y' be the node to erase.
            y = node_to_erase;
        }
        
        // If 'y' has a left child.
        if (y->get_left()) {
            // Let 'x' be the left child of 'y'.
            owned_x = y->move_left();
            x = owned_x.get();
        } else {
            // Let 'x' be the right child of 'y'.
            owned_x = y->move_right();
            x = owned_x.get();
        }

        // Exchange tree ownership between 'x' and 'y'.
        owned_y = y->get_owner().exchange(std::move(owned_x));

        // Save the color of 'y'.
        auto y_color = y->get_color();

        // If 'y' was not the node to erase.
        if (y != node_to_erase) {
            // Place 'y' where the node to erase is was.
            owned_y->set_left(node_to_erase->move_left());
            owned_y->set_right(node_to_erase->move_right());
            owned_y->set_color(node_to_erase->get_color());
            node_to_erase->get_owner().exchange(std::move(owned_y));
        }

        // If the color of 'y' is black.
        if ((nullptr != x) && (node::color::black == y_color)) {
            fix_erase_colors(x);
        }

        // Decrement the size.
        --m_size;
    }

    /**
     * Returns the beginning of the tree.
     */
    const_iterator begin() const
    {
        if (!m_root || !(*m_root)) {
            return{};
        }

        return const_iterator(m_left_most);
    }

    /**
     * Returns the end of the tree.
     */
    const_iterator end() const
    {
        if (!m_root || !(*m_root)) {
            return{};
        }

        return ++const_iterator(m_right_most);
    }

    /**
     * Returns the beginning of the tree.
     */
    const_iterator cbegin() const
    {
        if (!m_root || !(*m_root)) {
            return{};
        }

        return const_iterator(m_left_most);
    }

    /**
     * Returns the end of the tree.
     */
    const_iterator cend() const
    {
        if (!m_root || !(*m_root)) {
            return{};
        }

        return ++const_iterator(m_right_most);
    }

    /**
     * Returns the beginning of the tree.
     * For iteration in reverse order.
     */
    const_reverse_iterator rbegin() const
    {
        return const_reverse_iterator(end());
    }

    /**
     * Returns the end of the tree.
     * For iteration in reverse order.
     */
    const_reverse_iterator rend() const
    {
        return const_reverse_iterator(begin());
    }

    /**
     * Returns the beginning of the tree.
     * For iteration in reverse order.
     */
    const_reverse_iterator crbegin() const
    {
        return const_reverse_iterator(cend());
    }

    /**
     * Returns the end of the tree.
     * For iteration in reverse order.
     */
    const_reverse_iterator crend() const
    {
        return const_reverse_iterator(cbegin());
    }

    /**
     * Returns true if the tree is empty, else false.
     */
    bool empty() const
    {
        return (0 == m_size);
    }

    /**
     * Returns the size of the tree, that is, the number of nodes.
     */
    size_type size() const
    {
        return m_size;
    }

private:
    /**
     * Inserts a given node to the tree.
     */
    void insert_node(std::unique_ptr<node> node_to_insert)
    {
        // Start from the root of the tree.
        auto current_node = get_root();
        auto current_parent = static_cast<node *>(nullptr);
        
        // If there is no root.
        if (nullptr == current_node) {
            // Set this node as the left most and right most.
            m_left_most = node_to_insert.get();
            m_right_most = node_to_insert.get();

            // Set this node as the root node.
            set_root(std::move(node_to_insert));
            return;
        }

        // Find the proper insert location.
        while (nullptr != current_node) {
            // Set the current parent to the current node.
            current_parent = current_node;

            // If the value of the node to insert comes before the one of the current node.
            if (comes_before(node_to_insert->get_value(), current_node->get_value())) {
                // Advance to the left side of the tree.
                current_node = current_node->get_left();
            } else {
                // Advance to the right side of the tree.
                current_node = current_node->get_right();
            }
        }

        // We found a spot to insert the node.

        // Save a pointer to the node.
        auto weak_node_to_insert = node_to_insert.get();

        // If the value of the node to insert comes before the one of the current parent.
        if (comes_before(node_to_insert->get_value(), current_parent->get_value())) {
            // Insert the node as a left child.
            current_parent->set_left(std::move(node_to_insert));

            // If the parent is the left most, update the left most node.
            if (m_left_most == current_parent) {
                m_left_most = weak_node_to_insert;
            }
        } else {
            // Insert the node as a right child.
            current_parent->set_right(std::move(node_to_insert));

            // If the parent is the right most, update the right most node.
            if (m_right_most == current_parent) {
                m_right_most = weak_node_to_insert;
            }
        }

        // Set the color to red.
        weak_node_to_insert->set_color(node::color::red);

        // Set children to nullptr.
        weak_node_to_insert->set_left(nullptr);
        weak_node_to_insert->set_right(nullptr);

        // Fix the color errors caused by the insert.
        fix_insert_colors(weak_node_to_insert);
    }

    /**
     * Fixes color errors in the tree caused by an insert of the 
     * given node.
     */
    void fix_insert_colors(node * inserted_node)
    {
        // Start from the inserted node.
        auto current_node = inserted_node;

        // While the current node is not root , and its parent color is red.
        // Note: the virtual parent of the root node is the null node which is black.
        while (!current_node->is_root() &&
                current_node->get_parent()->get_color() == node::color::red) {

            // Save the grand parent.
            // Note: it exists because the parent is red, and therefore,
            //       is not the root node.
            auto grand_parent = current_node->get_parent()->get_parent();

            // If our parent is a left child.
            if (current_node->get_parent()->is_left_child()) {
                // Case 1 - if the grand parent's right child is red.
                if (grand_parent->is_right_color(node::color::red)) {
                    // Change parent to black.
                    current_node->get_parent()->set_color(node::color::black);

                    // Change grand parent right child to black.
                    grand_parent->get_right()->set_color(node::color::black);

                    // Change the grand parent to red.
                    grand_parent->set_color(node::color::red);

                    // Advance to the grand parent node.
                    current_node = grand_parent;

                    // Case 1 is finished.
                    continue;
                }

                // Case 2 - if the current node is a right child.
                // Note: After executing case 2, case 3 happens.
                if (current_node->is_right_child()) {
                    // Advance to the parent node.
                    current_node = current_node->get_parent();

                    // Rotate left around the current node.
                    current_node->rotate_left();
                }

                // Case 3 

                // Change the parent node to black.
                current_node->get_parent()->set_color(node::color::black);

                // Change the color of the grand parent to red.
                grand_parent->set_color(node::color::red);

                // Rotate right around the grand parent.
                grand_parent->rotate_right();

                // Left child case is done.
                continue;
            } // End of if (current_node->get_parent()->is_left_child())

            // Case 1 - if the grand parent's left child is red.
            if (grand_parent->is_left_color(node::color::red)) {
                // Change parent to black.
                current_node->get_parent()->set_color(node::color::black);

                // Change grand parent left child to black.
                grand_parent->get_left()->set_color(node::color::black);

                // Change the grand parent to red.
                grand_parent->set_color(node::color::red);

                // Advance to the grand parent node.
                current_node = grand_parent;

                // Case 1 is finished.
                continue;
            }

            // Case 2 - if the current node is a left child.
            // Note: After executing case 2, case 3 happens.
            if (current_node->is_left_child()) {
                // Advance to the parent node.
                current_node = current_node->get_parent();

                // Rotate right around the current node.
                current_node->rotate_right();
            }

            // Case 3 

            // Change the parent node to black.
            current_node->get_parent()->set_color(node::color::black);

            // Change the color of the grand parent to red.
            grand_parent->set_color(node::color::red);

            // Rotate left around the grand parent.
            grand_parent->rotate_left();

            // right child case is done.
            continue;
        }

        // Turn the root node to black.
        get_root()->set_color(node::color::black);
    }

    /**
     * Fixes color errors in the tree caused by erase.
     */
    void fix_erase_colors(node * fixup_node)
    {
        // Set the current node to the fix up node.
        auto current_node = fixup_node;

        // While the current node is not root and its color is black.
        while (!current_node->is_root() &&
                current_node->get_color() == node::color::black) {
            
            // If the current node is a left child.
            if (current_node->is_left_child()) {
                // Save the parent node.
                auto parent_node = current_node->get_parent();

                // Case 1 - If the color of the parent node's right child is red.
                // Note: if there is no right child, we know that the color of the null node is black.
                if (parent_node->is_right_color(node::color::red)) {

                    // Set the color of the parent node's right child to black.
                    parent_node->get_right()->set_color(node::color::black);
                    
                    // Set the parent node's color to red.
                    parent_node->set_color(node::color::red);
                    
                    // Rotate left around the parent node.
                    parent_node->rotate_left();

                    // Update the parent node.
                    parent_node = current_node->get_parent();
                }

                // Save the parent node's right child.
                auto parent_right_child = parent_node->get_right();

                // Case 2 - If both children of 'parent_right_child' are black.
                // Note: null nodes are referred to as black nodes.
                if (parent_right_child->is_left_color(node::color::black) && 
                    parent_right_child->is_right_color(node::color::black)) {

                    // Set its color to red.
                    parent_right_child->set_color(node::color::red);

                    // Advance to the parent node.
                    current_node = parent_node;
                } else if (parent_right_child->is_right_color(node::color::black)) {
                    // If the color of the parent node's right child is red, 
                    // change to black.
                    // Note: if the color is red, it is not the null node.
                    if (parent_right_child->is_left_color(node::color::red)) {
                        parent_right_child->get_left()->set_color(node::color::black);
                    }

                    // Set the parent's right child to red.
                    parent_right_child->set_color(node::color::red);

                    // Rotate right around the parent's right child.
                    parent_right_child->rotate_right();

                    // Update the parent node.
                    parent_node = current_node->get_parent();

                    // Update the parent's node right child.
                    parent_right_child = parent_node->get_right();
                }

                // Case 4.

                // Set the parent's right child color to the color of the parent node.
                parent_right_child->set_color(parent_node->get_color());

                // Set the parent node to black.
                parent_node->set_color(node::color::black);

                // If the color of the parent node's right child is red, 
                // change to black.
                // Note: if the color is red, it is not the null node.
                if (parent_right_child->is_right_color(node::color::red)) {
                    parent_right_child->get_right()->set_color(node::color::black);
                }

                // Rotate left around the parent node.
                parent_node->rotate_left();

                // Set the current node to be the root node.
                current_node = get_root();
                continue;
            }

            // The current node is a right child.

            // Save the parent node.
            auto parent_node = current_node->get_parent();

            // Case 1 - If the color of the parent node's left child is red.
            // Note: if there is no left child, we know that the color of the null node is black.
            if (parent_node->is_left_color(node::color::red)) {

                // Set the color of the parent node's left child to black.
                parent_node->get_left()->set_color(node::color::black);

                // Set the parent node's color to red.
                parent_node->set_color(node::color::red);

                // Rotate right around the parent node.
                parent_node->rotate_right();

                // Update the parent node.
                parent_node = current_node->get_parent();
            }

            // Save the parent node's left child.
            auto parent_left_child = parent_node->get_left();

            // Case 2 - If both children of 'parent_left_child' are black.
            // Note: null nodes are referred to as black nodes.
            if (parent_left_child->is_right_color(node::color::black) &&
                parent_left_child->is_left_color(node::color::black)) {

                // Set its color to red.
                parent_left_child->set_color(node::color::red);

                // Advance to the parent node.
                current_node = parent_node;
            } else if (parent_left_child->is_left_color(node::color::black)) {
                // If the color of the parent node's left child is red, 
                // change to black.
                // Note: if the color is red, it is not the null node.
                if (parent_left_child->is_right_color(node::color::red)) {
                    parent_left_child->get_right()->set_color(node::color::black);
                }

                // Set the parent's left child to red.
                parent_left_child->set_color(node::color::red);

                // Rotate left around the parent's left child.
                parent_left_child->rotate_left();

                // Update the parent node.
                parent_node = current_node->get_parent();

                // Update the parent's node left child.
                parent_left_child = parent_node->get_left();
            }

            // Case 4.

            // Set the parent's left child color to the color of the parent node.
            parent_left_child->set_color(parent_node->get_color());

            // Set the parent node to black.
            parent_node->set_color(node::color::black);

            // If the color of the parent node's left child is red, 
            // change to black.
            // Note: if the color is red, it is not the null node.
            if (parent_left_child->is_left_color(node::color::red)) {
                parent_left_child->get_left()->set_color(node::color::black);
            }

            // Rotate right around the parent node.
            parent_node->rotate_right();

            // Set the current node to be the root node.
            current_node = get_root();
        }

        // Set the color of the current node to black.
        current_node->set_color(node::color::black);
    }

    /**
     * Sets the root node of the tree.
     */
    void set_root(std::unique_ptr<node> root)
    {
        *m_root = std::move(root);
        get_root()->mark_as_root(*m_root);
    }

    /**
     * Returns the root node of the tree.
     */
    node * get_root() const
    {
        return (*m_root).get();
    }

    /**
     * Returns the left most node of the given tree node.
     */
    static node * get_left_most(node * tree_node)
    {
        auto left_most = tree_node;
        while (left_most->get_left()) {
            left_most = left_most->get_left();
        }
        return left_most;
    }

    /**
     * Returns the left most node of the given tree node.
     */
    static const node * get_left_most(const node * tree_node)
    {
        auto left_most = tree_node;
        while (left_most->get_left()) {
            left_most = left_most->get_left();
        }
        return left_most;
    }

    /**
     * Returns the right most node of the given tree node.
     */
    static node * get_right_most(node * tree_node)
    {
        auto right_most = tree_node;
        while (right_most->get_right()) {
            right_most = right_most->get_right();
        }
        return right_most;
    }

    /**
     * Returns the right most node of the given tree node.
     */
    static const node * get_right_most(const node * tree_node)
    {
        auto right_most = tree_node;
        while (right_most->get_right()) {
            right_most = right_most->get_right();
        }
        return right_most;
    }

    /**
     * Returns true if left should come before right.
     */
    static bool comes_before(const_reference left, const_reference right)
    {
        return key_compare()(left, right);
    }

    /**
     * Clones a tree.
     */
    static std::unique_ptr<node> clone(const node * root)
    {
        // If the root is null, return an empty node.
        if (!root) {
            return nullptr;
        }

        // Clone the root node.
        auto cloned = std::make_unique<node>(root->get_value());

        // Set the color to the color of the root.
        cloned->set_color(root->get_color());

        // If the root has a left child.
        if (root->get_left()) {
            // Clone the left subtree.
            cloned->set_left(clone(root->get_left()));
        }

        // If the root has a right child.
        if (root->get_right()) {
            // Clone the right subtree.
            cloned->set_right(clone(root->get_right()));
        }

        // Return the cloned tree.
        return cloned;
    }

private:
    /**
     * Pointer to the pointer to the root node.
     * Note: This is necessary because a rotate operation on the root node has to replace
     *       the root of the tree.
     */
    std::unique_ptr<std::unique_ptr<node>> m_root = std::make_unique<std::unique_ptr<node>>();

    /**
     * The size of the tree.
     */
    size_type m_size{};

    /**
     * The left most node.
     */
    node * m_left_most{};

    /**
     * The right most node.
     */
    node * m_right_most{};
};

/**
 * Swaps the left tree with the right tree.
 */
template <typename... Arguments>
void swap(red_black_tree<Arguments...> & left, red_black_tree<Arguments...> & right) noexcept
{
    left.swap(right);
}

} // zpp
